// Copyright 2017 Kisio Digital and/or its affiliates.
//
// This program is free software: you can redistribute it and/or
// modify it under the terms of the GNU General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see
// <http://www.gnu.org/licenses/>.

//! [GTFS](http://gtfs.org/) format management.

mod read;
mod write;

use crate::collection::CollectionWithId;
use crate::collection::Idx;
use crate::common_format;
use crate::common_format::{manage_calendars, Availability};
use crate::gtfs::read::EquipmentList;
use crate::model::{Collections, Model};
use crate::objects;
use crate::objects::Time;
use crate::objects::{StopPoint, StopType};
use crate::read_utils;
use crate::read_utils::add_prefix;
use crate::utils::*;
use crate::Result;
use derivative::Derivative;
use log::info;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::fs::File;
use std::path::Path;

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
struct Agency {
    #[serde(rename = "agency_id")]
    id: Option<String>,
    #[serde(rename = "agency_name")]
    name: String,
    #[serde(rename = "agency_url")]
    url: String,
    #[serde(rename = "agency_timezone")]
    timezone: String,
    #[serde(rename = "agency_lang")]
    lang: Option<String>,
    #[serde(rename = "agency_phone")]
    phone: Option<String>,
    #[serde(rename = "agency_email")]
    email: Option<String>,
}

impl<'a> From<&'a objects::Network> for Agency {
    fn from(obj: &objects::Network) -> Agency {
        Agency {
            id: Some(obj.id.clone()),
            name: obj.name.clone(),
            url: obj
                .url
                .clone()
                .unwrap_or_else(|| "http://www.navitia.io/".to_string()),
            timezone: obj
                .timezone
                .clone()
                .unwrap_or_else(|| "Europe/Paris".to_string()),
            lang: obj.lang.clone(),
            phone: obj.phone.clone(),
            email: None,
        }
    }
}

#[derivative(Default)]
#[derive(Derivative, Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
enum StopLocationType {
    #[derivative(Default)]
    #[serde(rename = "0")]
    StopPoint,
    #[serde(rename = "1")]
    StopArea,
    #[serde(rename = "2")]
    StopEntrance,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
struct Stop {
    #[serde(rename = "stop_id", deserialize_with = "de_without_slashes")]
    id: String,
    #[serde(rename = "stop_code")]
    code: Option<String>,
    #[serde(rename = "stop_name")]
    name: String,
    #[serde(default, rename = "stop_desc")]
    desc: String,
    #[serde(
        rename = "stop_lon",
        deserialize_with = "de_location_trim_with_default"
    )]
    lon: f64,
    #[serde(
        rename = "stop_lat",
        deserialize_with = "de_location_trim_with_default"
    )]
    lat: f64,
    #[serde(rename = "zone_id")]
    fare_zone_id: Option<String>,
    #[serde(rename = "stop_url")]
    url: Option<String>,
    #[serde(default, deserialize_with = "de_with_empty_default")]
    location_type: StopLocationType,
    #[serde(default, deserialize_with = "de_option_without_slashes")]
    parent_station: Option<String>,
    #[serde(rename = "stop_timezone")]
    timezone: Option<String>,
    #[serde(deserialize_with = "de_with_empty_default", default)]
    wheelchair_boarding: Availability,
    platform_code: Option<String>,
}

#[derive(Derivative)]
#[derivative(Default)]
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
enum DirectionType {
    #[derivative(Default)]
    #[serde(rename = "0")]
    Forward,
    #[serde(rename = "1")]
    Backward,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
struct Trip {
    route_id: String,
    service_id: String,
    #[serde(rename = "trip_id")]
    id: String,
    #[serde(rename = "trip_headsign")]
    headsign: Option<String>,
    #[serde(rename = "trip_short_name")]
    short_name: Option<String>,
    #[serde(
        default,
        deserialize_with = "de_with_empty_default",
        rename = "direction_id"
    )]
    direction: DirectionType,
    block_id: Option<String>,
    #[serde(default, deserialize_with = "de_option_without_slashes")]
    shape_id: Option<String>,
    #[serde(deserialize_with = "de_with_empty_default", default)]
    wheelchair_accessible: Availability,
    #[serde(deserialize_with = "de_with_empty_default", default)]
    bikes_allowed: Availability,
}

fn default_true_bool() -> bool {
    true
}

#[derive(Serialize, Deserialize, Debug, Clone)]
struct StopTime {
    trip_id: String,
    arrival_time: Option<Time>,
    departure_time: Option<Time>,
    #[serde(deserialize_with = "de_without_slashes")]
    stop_id: String,
    stop_sequence: u32,
    #[serde(deserialize_with = "de_with_empty_default", default)]
    pickup_type: u8,
    #[serde(deserialize_with = "de_with_empty_default", default)]
    drop_off_type: u8,
    local_zone_id: Option<u16>,
    stop_headsign: Option<String>,
    #[serde(
        deserialize_with = "de_from_u8_with_true_default",
        serialize_with = "ser_from_bool",
        default = "default_true_bool"
    )]
    timepoint: bool,
}

#[derive(Serialize, Deserialize, Debug, Derivative, PartialEq)]
#[derivative(Default)]
enum TransferType {
    #[derivative(Default)]
    #[serde(rename = "0")]
    Recommended,
    #[serde(rename = "1")]
    Timed,
    #[serde(rename = "2")]
    WithTransferTime,
    #[serde(rename = "3")]
    NotPossible,
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
struct Transfer {
    #[serde(deserialize_with = "de_without_slashes")]
    from_stop_id: String,
    #[serde(deserialize_with = "de_without_slashes")]
    to_stop_id: String,
    #[serde(deserialize_with = "de_with_empty_default")]
    transfer_type: TransferType,
    min_transfer_time: Option<u32>,
}

impl<'a> From<&'a objects::Transfer> for Transfer {
    fn from(obj: &objects::Transfer) -> Transfer {
        Transfer {
            from_stop_id: obj.from_stop_id.clone(),
            to_stop_id: obj.to_stop_id.clone(),
            transfer_type: TransferType::WithTransferTime,
            min_transfer_time: obj.min_transfer_time,
        }
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
struct Shape {
    #[serde(rename = "shape_id", deserialize_with = "de_without_slashes")]
    id: String,
    #[serde(rename = "shape_pt_lat")]
    lat: f64,
    #[serde(rename = "shape_pt_lon")]
    lon: f64,
    #[serde(rename = "shape_pt_sequence")]
    sequence: u32,
}

fn read<H>(
    file_handler: &mut H,
    config_path: Option<impl AsRef<Path>>,
    prefix: Option<String>,
) -> Result<Model>
where
    for<'a> &'a mut H: read_utils::FileHandler,
{
    let mut collections = Collections::default();
    let mut equipments = EquipmentList::default();
    let mut comments: CollectionWithId<objects::Comment> = CollectionWithId::default();

    manage_calendars(file_handler, &mut collections)?;

    let (contributors, mut datasets, feed_infos) = read_utils::read_config(config_path)?;
    read_utils::set_dataset_validity_period(&mut datasets, &collections.calendars)?;

    collections.contributors = contributors;
    collections.datasets = datasets;
    collections.feed_infos = feed_infos;

    let (networks, companies) = read::read_agency(file_handler)?;
    collections.networks = networks;
    collections.companies = companies;
    let (stop_areas, stop_points) = read::read_stops(file_handler, &mut comments, &mut equipments)?;
    collections.transfers = read::read_transfers(file_handler, &stop_points)?;
    collections.stop_areas = stop_areas;
    collections.stop_points = stop_points;

    read::manage_shapes(&mut collections, file_handler)?;

    read::read_routes(file_handler, &mut collections)?;
    collections.equipments = CollectionWithId::new(equipments.into_equipments())?;
    collections.comments = comments;
    read::manage_stop_times(&mut collections, file_handler)?;
    read::manage_frequencies(&mut collections, file_handler)?;

    collections.sanitize()?;

    //add prefixes
    if let Some(prefix) = prefix {
        add_prefix(prefix, &mut collections)?;
    }

    Ok(Model::new(collections)?)
}

/// Imports a `Model` from the [GTFS](http://gtfs.org/) files in the
/// `path` directory.
///
/// The `config_path` argument allows you to give a path to a file
/// containing a json representing the contributor and dataset used
/// for this GTFS. If not given, default values will be created.
///
/// The `prefix` argument is a string that will be prepended to every
/// identifiers, allowing to namespace the dataset. By default, no
/// prefix will be added to the identifiers.
pub fn read_from_path<P: AsRef<Path>>(
    p: P,
    config_path: Option<P>,
    prefix: Option<String>,
) -> Result<Model> {
    let mut file_handle = read_utils::PathFileHandler::new(p.as_ref().to_path_buf());
    read(&mut file_handle, config_path, prefix)
}

/// Imports a `Model` from a zip file containing the [GTFS](http://gtfs.org/).
///
/// The `config_path` argument allows you to give a path to a file
/// containing a json representing the contributor and dataset used
/// for this GTFS. If not given, default values will be created.
///
/// The `prefix` argument is a string that will be prepended to every
/// identifiers, allowing to namespace the dataset. By default, no
/// prefix will be added to the identifiers.
pub fn read_from_zip<P: AsRef<Path>>(
    p: P,
    config_path: Option<P>,
    prefix: Option<String>,
) -> Result<Model> {
    let reader = File::open(p.as_ref())?;
    let mut file_handle = read_utils::ZipHandler::new(reader, p)?;
    read(&mut file_handle, config_path, prefix)
}

/// Imports a `Model` from a url hosting a zip file containing the [GTFS](http://gtfs.org/).
///
/// The `config_path` argument allows you to give a path to a file
/// containing a json representing the contributor and dataset used
/// for this GTFS. If not given, default values will be created.
///
/// The `prefix` argument is a string that will be prepended to every
/// identifiers, allowing to namespace the dataset. By default, no
/// prefix will be added to the identifiers.
pub fn read_from_url<P: AsRef<Path>>(
    url: &str,
    config_path: Option<P>,
    prefix: Option<String>,
) -> Result<Model> {
    let reader = read_utils::read_url(&url)?;
    let mut file_handle = read_utils::ZipHandler::new(reader, &url)?;
    read(&mut file_handle, config_path, prefix)
}

#[derive(PartialOrd, Ord, Debug, Clone, Eq, PartialEq, Hash)]
enum RouteType {
    Tramway,
    Metro,
    Train,
    Bus,
    Ferry,
    CableCar,
    SuspendedCableCar,
    Funicular,
    Coach,
    Air,
    Taxi,
    UnknownMode,
}
impl fmt::Display for RouteType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
struct Route {
    #[serde(rename = "route_id")]
    id: String,
    agency_id: Option<String>,
    #[serde(rename = "route_short_name")]
    short_name: String,
    #[serde(rename = "route_long_name")]
    long_name: String,
    #[serde(rename = "route_desc")]
    desc: Option<String>,
    route_type: RouteType,
    #[serde(rename = "route_url")]
    url: Option<String>,
    #[serde(
        rename = "route_color",
        default,
        deserialize_with = "de_with_empty_or_invalid_default"
    )]
    color: Option<objects::Rgb>,
    #[serde(
        rename = "route_text_color",
        default,
        deserialize_with = "de_with_empty_or_invalid_default"
    )]
    text_color: Option<objects::Rgb>,
    #[serde(rename = "route_sort_order")]
    sort_order: Option<u32>,
}

fn remove_stop_zones(model: Model) -> Result<Collections> {
    let mut collections = model.into_collections();
    collections
        .stop_points
        .retain(|sp| sp.stop_type != StopType::Zone);
    let stop_point_ids: Vec<&Idx<StopPoint>> =
        collections.stop_points.get_id_to_idx().values().collect();
    let mut vjs = collections.vehicle_journeys.take();
    for vj in &mut vjs {
        vj.stop_times
            .retain(|st| stop_point_ids.contains(&&st.stop_point_idx));
    }
    vjs.retain(|vj| !vj.stop_times.is_empty());
    collections.vehicle_journeys = CollectionWithId::new(vjs)?;
    Ok(collections)
}

/// Exports a `Model` to [GTFS](http://gtfs.org/) files
/// in the given directory.
/// see [NTFS to GTFS conversion](https://github.com/CanalTP/transit_model/blob/master/src/documentation/ntfs2gtfs.md)
pub fn write<P: AsRef<Path>>(model: Model, path: P) -> Result<()> {
    let mut collections = remove_stop_zones(model)?;
    collections.sanitize()?;
    let model = Model::new(collections)?;
    let path = path.as_ref();
    info!("Writing GTFS to {:?}", path);

    write::write_transfers(path, &model.transfers)?;
    write::write_agencies(path, &model.networks)?;
    common_format::write_calendar_dates(path, &model.calendars)?;
    write::write_stops(
        path,
        &model.stop_points,
        &model.stop_areas,
        &model.comments,
        &model.equipments,
    )?;
    write::write_trips(
        path,
        &model.vehicle_journeys,
        &model.stop_points,
        &model.routes,
        &model.trip_properties,
    )?;
    write::write_routes(path, &model)?;
    write::write_stop_extensions(path, &model.stop_points, &model.stop_areas)?;
    write::write_stop_times(
        path,
        &model.vehicle_journeys,
        &model.stop_points,
        &model.stop_time_headsigns,
    )?;
    write::write_shapes(path, &model.geometries)?;

    Ok(())
}
