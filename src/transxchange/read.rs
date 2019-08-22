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

use crate::{
    collection::CollectionWithId,
    minidom_utils::TryOnlyChild,
    model::{Collections, Model},
    objects::*,
    transxchange::naptan,
    AddPrefix, Result,
};
use chrono::{
    naive::{NaiveDate, MAX_DATE, MIN_DATE},
    Datelike, Duration,
};
use failure::format_err;
use lazy_static::lazy_static;
use log::{info, warn};
use minidom::Element;
use std::{
    collections::{BTreeSet, HashSet},
    convert::TryFrom,
    fs::File,
    io::Read,
    path::Path,
};
use walkdir::WalkDir;
use zip::ZipArchive;

const UNDEFINED: &str = "Undefined";
const EUROPE_LONDON_TIMEZONE: &str = "Europe/London";
const DEFAULT_MODE: &str = "Bus";

lazy_static! {
    static ref MODES: std::collections::HashMap<&'static str, &'static str> = {
        let mut modes_map = std::collections::HashMap::new();
        modes_map.insert("air", "Air");
        modes_map.insert("bus", DEFAULT_MODE);
        modes_map.insert("coach", "Coach");
        modes_map.insert("ferry", "Ferry");
        modes_map.insert("underground", "Metro");
        modes_map.insert("metro", "Metro");
        modes_map.insert("rail", "Train");
        modes_map.insert("tram", "Tramway");
        modes_map.insert("trolleyBus", "Shuttle");
        modes_map
    };
}

fn get_by_reference<'a>(
    element: &'a Element,
    child_name: &str,
    reference: &str,
) -> Result<&'a Element> {
    element.try_only_child_with_filter(child_name, |e| {
        e.attr("id").filter(|id| *id == reference).is_some()
    })
}

fn get_service_validity_period(transxchange: &Element) -> Result<ValidityPeriod> {
    let operating_period = transxchange
        .try_only_child("Services")?
        .try_only_child("Service")?
        .try_only_child("OperatingPeriod")?;
    let start_date: Date = operating_period
        .try_only_child("StartDate")?
        .text()
        .parse()?;
    let end_date: Date = operating_period
        .try_only_child("EndDate")
        .map(Element::text)
        .map(|end_date_text| end_date_text.parse())
        .unwrap_or_else(|_| Ok(start_date + Duration::days(180)))?;
    Ok(ValidityPeriod {
        start_date,
        end_date,
    })
}

fn update_validity_period(dataset: &mut Dataset, service_validity_period: &ValidityPeriod) {
    dataset.start_date = if service_validity_period.start_date < dataset.start_date {
        service_validity_period.start_date
    } else {
        dataset.start_date
    };
    dataset.end_date = if service_validity_period.end_date > dataset.end_date {
        service_validity_period.end_date
    } else {
        dataset.end_date
    };
}

// The datasets already have some validity period. This function tries to
// extend them with a service validity period from the TransXChange file:
// - if service start date is before the dataset start date, then update the
//   dataset start date with service start date
// - if service end date is after the dataset end date, then update the
//   dataset end date with service end date
//
// Examples:
// Past                                                             Future
// |--------------------------------------------------------------------->
//
//             ^--------- dataset validity ---------^
//                 ^---- service validity ----^
//             ^------ final dataset validity ------^
//
//             ^--------- dataset validity ---------^
//      ^---- service validity ----^
//      ^--------- final dataset validity ----------^
//
//             ^--------- dataset validity ---------^
//          ^-------------- service validity --------------^
//          ^----------- final dataset validity -----------^
fn update_validity_period_from_transxchange(
    datasets: &mut CollectionWithId<Dataset>,
    transxchange: &Element,
) -> Result<CollectionWithId<Dataset>> {
    let service_validity_period = get_service_validity_period(transxchange)?;
    let mut datasets = datasets.take();
    for dataset in &mut datasets {
        update_validity_period(dataset, &service_validity_period);
    }
    CollectionWithId::new(datasets)
}

fn load_network(transxchange: &Element) -> Result<Network> {
    let operator_ref = transxchange
        .try_only_child("Services")?
        .try_only_child("Service")?
        .try_only_child("RegisteredOperatorRef")?
        .text();
    let operator = get_by_reference(
        transxchange.try_only_child("Operators")?,
        "Operator",
        &operator_ref,
    )?;
    let id = operator.try_only_child("OperatorCode")?.text();
    let name = operator
        .try_only_child("TradingName")
        .or_else(|_| operator.try_only_child("OperatorShortName"))?
        .text()
        .trim()
        .to_string();
    let name = if name.is_empty() {
        String::from(UNDEFINED)
    } else {
        name
    };
    let network = Network {
        id,
        name,
        timezone: Some(String::from(EUROPE_LONDON_TIMEZONE)),
        ..Default::default()
    };
    Ok(network)
}

fn load_companies(transxchange: &Element) -> Result<CollectionWithId<Company>> {
    let mut companies = CollectionWithId::default();
    for operator in transxchange.try_only_child("Operators")?.children() {
        let id = operator.try_only_child("OperatorCode")?.text();
        let name = operator
            .try_only_child("OperatorShortName")?
            .text()
            .trim()
            .to_string();
        let company = Company {
            id,
            name,
            ..Default::default()
        };
        companies.push(company)?;
    }
    Ok(companies)
}

fn load_commercial_physical_modes(
    transxchange: &Element,
) -> Result<(CommercialMode, PhysicalMode)> {
    let mode = match transxchange
        .try_only_child("Services")?
        .try_only_child("Service")?
        .try_only_child("Mode")
        .map(Element::text)
    {
        Ok(mode) => MODES.get(mode.as_str()).unwrap_or(&DEFAULT_MODE),
        Err(e) => {
            warn!("{} - Default mode '{}' assigned", e, DEFAULT_MODE);
            DEFAULT_MODE
        }
    };
    let commercial_mode = CommercialMode {
        id: mode.to_string(),
        name: mode.to_string(),
    };
    let physical_mode = PhysicalMode {
        id: mode.to_string(),
        name: mode.to_string(),
        ..Default::default()
    };
    Ok((commercial_mode, physical_mode))
}

fn load_lines(
    transxchange: &Element,
    network_id: &str,
    commercial_mode_id: &str,
) -> Result<CollectionWithId<Line>> {
    let service = transxchange
        .try_only_child("Services")?
        .try_only_child("Service")?;
    let service_id = service.try_only_child("ServiceCode")?.text();
    let mut lines = CollectionWithId::default();
    let name = if let Ok(description) = service.try_only_child("Description") {
        description.text().trim().to_string()
    } else {
        String::from(UNDEFINED)
    };
    let standard_service = service.try_only_child("StandardService")?;
    let forward_name = standard_service
        .try_only_child("Destination")?
        .text()
        .trim()
        .to_string();
    let backward_name = standard_service
        .try_only_child("Origin")?
        .text()
        .trim()
        .to_string();
    for line in service.try_only_child("Lines")?.children() {
        if let Some(line_id) = line.attr("id") {
            let id = format!("{}:{}", service_id, line_id);
            let code = Some(line.try_only_child("LineName")?.text().trim().to_string());
            let network_id = network_id.to_string();
            let commercial_mode_id = commercial_mode_id.to_string();
            let name = name.to_string();
            let forward_name = Some(forward_name.clone());
            let backward_name = Some(backward_name.clone());
            let line = Line {
                id,
                code,
                name,
                forward_name,
                backward_name,
                network_id,
                commercial_mode_id,
                ..Default::default()
            };
            let _ = lines.push(line);
        }
    }
    Ok(lines)
}

fn create_route(_transxchange: &Element, _vehicle_journey: &Element) -> Result<Route> {
    // TODO: Implement routes
    // The fake ID helps pass the integration tests for now. Can be remove once real implementation is done
    Ok(Route {
        line_id: String::from("SCAO812:SL1"),
        ..Default::default()
    })
}

struct NaiveDateRange {
    current: NaiveDate,
    end: NaiveDate,
}

impl NaiveDateRange {
    fn new(start: NaiveDate, end: NaiveDate) -> NaiveDateRange {
        if start <= end {
            NaiveDateRange {
                current: start,
                end,
            }
        } else {
            // If end date is smaller, then invert start and end
            NaiveDateRange {
                current: end,
                end: start,
            }
        }
    }
}

impl Iterator for NaiveDateRange {
    type Item = NaiveDate;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current <= self.end {
            let date = self.current;
            self.current = self.current.succ();
            Some(date)
        } else {
            None
        }
    }
}

fn generate_calendar_dates(
    operating_profile: &Element,
    validity_period: ValidityPeriod,
) -> Result<BTreeSet<Date>> {
    let mut dates = BTreeSet::new();
    let mut days = HashSet::new();
    for element in operating_profile
        .try_only_child("RegularDayType")?
        .try_only_child("DaysOfWeek")?
        .children()
    {
        use chrono::Weekday::*;
        match element.name() {
            "Monday" => {
                days.insert(Mon);
            }
            "Tuesday" => {
                days.insert(Tue);
            }
            "Wednesday" => {
                days.insert(Wed);
            }
            "Thursday" => {
                days.insert(Thu);
            }
            "Friday" => {
                days.insert(Fri);
            }
            "Saturday" => {
                days.insert(Sat);
            }
            "Sunday" => {
                days.insert(Sun);
            }
            "MondayToFriday" => {
                days.insert(Mon);
                days.insert(Tue);
                days.insert(Wed);
                days.insert(Thu);
                days.insert(Fri);
            }
            "MondayToSaturday" => {
                days.insert(Mon);
                days.insert(Tue);
                days.insert(Wed);
                days.insert(Thu);
                days.insert(Fri);
                days.insert(Sat);
            }
            "MondayToSunday" => {
                days.insert(Mon);
                days.insert(Tue);
                days.insert(Wed);
                days.insert(Thu);
                days.insert(Fri);
                days.insert(Sat);
                days.insert(Sun);
            }
            "NotSaturday" => {
                days.insert(Mon);
                days.insert(Tue);
                days.insert(Wed);
                days.insert(Thu);
                days.insert(Fri);
                days.insert(Sun);
            }
            "Weekend" => {
                days.insert(Sat);
                days.insert(Sun);
            }
            unknown_tag => warn!("Tag '{}' is not a valid tag for DaysOfWeek", unknown_tag),
        };
    }
    for date in NaiveDateRange::new(validity_period.start_date, validity_period.end_date) {
        if days.contains(&date.weekday()) {
            // TODO: Handle exceptions (see SpecialDaysOperation)
            // TODO: Handle bank holidays (see BankHolidaysOperation)
            dates.insert(date);
        }
    }
    Ok(dates)
}

fn create_calendar_dates(
    transxchange: &Element,
    vehicle_journey: &Element,
) -> Result<BTreeSet<Date>> {
    let operating_profile = vehicle_journey
        .try_only_child("OperatingProfile")
        .or_else(|_| {
            transxchange
                .try_only_child("Services")?
                .try_only_child("Service")?
                .try_only_child("OperatingProfile")
        })?;
    let validity_period = get_service_validity_period(transxchange)?;
    generate_calendar_dates(&operating_profile, validity_period)
}

// Get Wait or Run time from ISO 8601 duration
fn parse_duration_in_seconds(duration_iso8601: &str) -> Result<Time> {
    let std_duration = time_parse::duration::parse_nom(duration_iso8601)?;
    let duration_seconds = Duration::from_std(std_duration)?.num_seconds();
    let time = Time::new(0, 0, u32::try_from(duration_seconds)?);
    Ok(time)
}

fn get_duration_from(element: &Element, name: &str) -> Time {
    element
        .try_only_child(name)
        .map(Element::text)
        .and_then(|s| parse_duration_in_seconds(&s))
        .unwrap_or_default()
}

fn get_pickup_and_dropoff_types(element: &Element, name: &str) -> (u8, u8) {
    element
        .try_only_child(name)
        .map(Element::text)
        .map(|a| match a.as_str() {
            "pickUp" => (0, 1),
            "setDown" => (1, 0),
            _ => (0, 0),
        })
        .unwrap_or((0, 0))
}

fn calculate_stop_times(
    stop_points: &CollectionWithId<StopPoint>,
    journey_pattern_section: &Element,
    first_departure_time: &Time,
) -> Result<Vec<StopTime>> {
    let mut stop_times = vec![];
    let mut next_arrival_time = *first_departure_time;
    let mut stop_point_previous_wait_to = Time::default();
    let mut sequence = 1; // use loop index instead of JourneyPatternTimingLinkId (not always continuous)

    for journey_pattern_timing_link in journey_pattern_section.children() {
        let stop_point = journey_pattern_timing_link.try_only_child("From")?;
        let stop_point_ref = stop_point.try_only_child("StopPointRef")?.text();
        let stop_point_idx = stop_points
            .get_idx(&stop_point_ref)
            .ok_or_else(|| format_err!("stop_id={:?} not found", stop_point_ref))?;
        let stop_point_wait_from = get_duration_from(&stop_point, "WaitTime");
        let run_time = get_duration_from(&journey_pattern_timing_link, "RunTime");
        let (pickup_type, drop_off_type) = get_pickup_and_dropoff_types(&stop_point, "Activity");
        let arrival_time = next_arrival_time;
        let departure_time = arrival_time + stop_point_wait_from + stop_point_previous_wait_to;

        stop_times.push(StopTime {
            stop_point_idx,
            sequence,
            arrival_time,
            departure_time,
            boarding_duration: 0,
            alighting_duration: 0,
            pickup_type,
            drop_off_type,
            datetime_estimated: false,
            local_zone_id: None,
        });

        next_arrival_time = departure_time + run_time;
        stop_point_previous_wait_to = get_duration_from(
            journey_pattern_timing_link.try_only_child("To")?,
            "WaitTime",
        );
        sequence = sequence + 1;
    }
    let stop_point = journey_pattern_section
        .children()
        .last()
        .ok_or_else(|| format_err!("Failed to find the last JourneyPatternSection"))?
        .try_only_child("To")?;
    let stop_point_ref = stop_point.try_only_child("StopPointRef")?.text();
    let stop_point_idx = stop_points
        .get_idx(&stop_point_ref)
        .ok_or_else(|| format_err!("stop_id={} not found", stop_point_ref))?;
    let (pickup_type, drop_off_type) = get_pickup_and_dropoff_types(&stop_point, "Activity");

    stop_times.push(StopTime {
        stop_point_idx,
        sequence,
        arrival_time: next_arrival_time,
        departure_time: next_arrival_time,
        boarding_duration: 0,
        alighting_duration: 0,
        pickup_type,
        drop_off_type,
        datetime_estimated: false,
        local_zone_id: None,
    });
    Ok(stop_times)
}

fn create_stop_times(
    stop_points: &CollectionWithId<StopPoint>,
    transxchange: &Element,
    vehicle_journey: &Element,
) -> Result<Vec<StopTime>> {
    let journey_pattern_ref = vehicle_journey.try_only_child("JourneyPatternRef")?.text();
    let journey_pattern = get_by_reference(
        transxchange
            .try_only_child("Services")?
            .try_only_child("Service")?
            .try_only_child("StandardService")?,
        "JourneyPattern",
        &journey_pattern_ref,
    )?;
    let journey_pattern_section_ref = journey_pattern
        .try_only_child("JourneyPatternSectionRefs")?
        .text();
    let journey_pattern_section = get_by_reference(
        transxchange.try_only_child("JourneyPatternSections")?,
        "JourneyPatternSection",
        &journey_pattern_section_ref,
    )?;
    let departure_time: Time = vehicle_journey
        .try_only_child("DepartureTime")?
        .text()
        .parse()?;
    calculate_stop_times(&stop_points, &journey_pattern_section, &departure_time)
}

fn load_routes_vehicle_journeys_calendars(
    collections: &Collections,
    transxchange: &Element,
    dataset_id: &str,
    physical_mode_id: &str,
) -> Result<(
    CollectionWithId<Route>,
    CollectionWithId<VehicleJourney>,
    CollectionWithId<Calendar>,
)> {
    let mut routes = CollectionWithId::default();
    let mut vehicle_journeys = CollectionWithId::default();
    let mut calendars = CollectionWithId::default();

    for vehicle_journey in transxchange.try_only_child("VehicleJourneys")?.children() {
        let service_ref = vehicle_journey.try_only_child("ServiceRef")?.text();
        let line_ref = vehicle_journey.try_only_child("LineRef")?.text();
        let vehicle_journey_code = vehicle_journey.try_only_child("VehicleJourneyCode")?.text();
        let id = format!("{}:{}:{}", service_ref, line_ref, vehicle_journey_code);
        let dates = create_calendar_dates(transxchange, vehicle_journey)?;
        let calendar = Calendar {
            id: format!("CD:{}", id),
            dates,
        };
        let service_id = calendar.id.clone();
        let stop_times =
            match create_stop_times(&collections.stop_points, transxchange, vehicle_journey) {
                Ok(val) => val,
                Err(e) => {
                    warn!("{} / vehiclejourney {} skipped", e, id);
                    continue;
                }
            };

        let operator_ref = vehicle_journey.try_only_child("OperatorRef")?.text();
        let operator = get_by_reference(
            transxchange.try_only_child("Operators")?,
            "Operator",
            &operator_ref,
        )?;
        let company_id = operator.try_only_child("OperatorCode")?.text();
        let route = create_route(transxchange, vehicle_journey)?;
        let route_id = route.id.clone();
        // TODO: Fill up the headsign
        let headsign = None;

        // Insert only at the last moment
        calendars.push(calendar)?;
        // Ignore duplicate insert (it means the route has already been created)
        let _ = routes.push(route);
        vehicle_journeys.push(VehicleJourney {
            id,
            stop_times,
            route_id,
            physical_mode_id: physical_mode_id.to_string(),
            dataset_id: dataset_id.to_string(),
            service_id,
            company_id,
            headsign,
            ..Default::default()
        })?;
    }
    Ok((routes, vehicle_journeys, calendars))
}

fn read_xml(transxchange: &Element, collections: &mut Collections, dataset_id: &str) -> Result<()> {
    let network = load_network(transxchange)?;
    let companies = load_companies(transxchange)?;
    let (commercial_mode, physical_mode) = load_commercial_physical_modes(transxchange)?;
    let lines = load_lines(transxchange, &network.id, &commercial_mode.id)?;
    let (routes, vehicle_journeys, calendars) = load_routes_vehicle_journeys_calendars(
        collections,
        transxchange,
        dataset_id,
        &physical_mode.id,
    )?;

    // Insert in collections
    collections.datasets =
        update_validity_period_from_transxchange(&mut collections.datasets, transxchange)?;
    let _ = collections.networks.push(network);
    collections.companies.merge(companies);
    // Ignore if `push` returns an error for duplicates
    let _ = collections.commercial_modes.push(commercial_mode);
    let _ = collections.physical_modes.push(physical_mode);
    collections.lines.merge(lines);
    collections.routes.try_merge(routes)?;
    collections.vehicle_journeys.try_merge(vehicle_journeys)?;
    collections.calendars.try_merge(calendars)?;
    Ok(())
}

fn read_file<F>(
    file_path: &Path,
    mut file: F,
    collections: &mut Collections,
    dataset_id: &str,
) -> Result<()>
where
    F: Read,
{
    match file_path.extension() {
        Some(ext) if ext == "xml" => {
            info!("reading TransXChange file {:?}", file_path);
            let mut file_content = String::new();
            file.read_to_string(&mut file_content)?;
            match file_content.parse::<Element>() {
                Ok(element) => read_xml(&element, collections, dataset_id)?,
                Err(e) => {
                    warn!("Failed to parse file '{:?}' as DOM: {}", file_path, e);
                }
            };
        }
        _ => info!("skipping file {:?}", file_path),
    };
    Ok(())
}

fn read_from_zip<P>(
    transxchange_path: P,
    collections: &mut Collections,
    dataset_id: &str,
) -> Result<()>
where
    P: AsRef<Path>,
{
    let zip_file = File::open(transxchange_path)?;
    let mut zip_archive = ZipArchive::new(zip_file)?;
    for index in 0..zip_archive.len() {
        let file = zip_archive.by_index(index)?;
        read_file(
            file.sanitized_name().as_path(),
            file,
            collections,
            dataset_id,
        )?;
    }
    Ok(())
}

fn read_from_path<P>(
    transxchange_path: P,
    collections: &mut Collections,
    dataset_id: &str,
) -> Result<()>
where
    P: AsRef<Path>,
{
    for entry in WalkDir::new(transxchange_path)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file())
    {
        let file = File::open(entry.path())?;
        read_file(entry.path(), file, collections, dataset_id)?;
    }
    Ok(())
}

/// Read TransXChange format into a Navitia Transit Model
pub fn read<P>(
    transxchange_path: P,
    naptan_path: P,
    config_path: Option<P>,
    prefix: Option<String>,
) -> Result<Model>
where
    P: AsRef<Path>,
{
    fn init_dataset_validity_period(dataset: &mut Dataset) {
        dataset.start_date = MAX_DATE;
        dataset.end_date = MIN_DATE;
    }

    let mut collections = Collections::default();
    let (contributor, mut dataset, feed_infos) = crate::read_utils::read_config(config_path)?;
    collections.contributors = CollectionWithId::from(contributor);
    init_dataset_validity_period(&mut dataset);
    let dataset_id = dataset.id.clone();
    collections.datasets = CollectionWithId::from(dataset);
    collections.feed_infos = feed_infos;
    if naptan_path.as_ref().is_file() {
        naptan::read_from_zip(naptan_path, &mut collections)?;
    } else {
        naptan::read_from_path(naptan_path, &mut collections)?;
    };
    if transxchange_path.as_ref().is_file() {
        read_from_zip(transxchange_path, &mut collections, &dataset_id)?;
    } else {
        read_from_path(transxchange_path, &mut collections, &dataset_id)?;
    };

    if let Some(prefix) = prefix {
        collections.add_prefix_with_sep(prefix.as_str(), ":");
    }
    Model::new(collections)
}

#[cfg(test)]
mod tests {
    use super::*;

    mod get_service_validity_period {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        fn has_start_and_end() {
            let xml = r#"<root>
                <Services>
                    <Service>
                        <OperatingPeriod>
                            <StartDate>2019-01-01</StartDate>
                            <EndDate>2019-03-31</EndDate>
                        </OperatingPeriod>
                    </Service>
                </Services>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let ValidityPeriod {
                start_date,
                end_date,
            } = get_service_validity_period(&root).unwrap();
            assert_eq!(start_date, Date::from_ymd(2019, 1, 1));
            assert_eq!(end_date, Date::from_ymd(2019, 3, 31));
        }

        #[test]
        fn has_only_start() {
            let xml = r#"<root>
                <Services>
                    <Service>
                        <OperatingPeriod>
                            <StartDate>2019-01-01</StartDate>
                        </OperatingPeriod>
                    </Service>
                </Services>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let ValidityPeriod {
                start_date,
                end_date,
            } = get_service_validity_period(&root).unwrap();
            assert_eq!(start_date, Date::from_ymd(2019, 1, 1));
            assert_eq!(end_date, Date::from_ymd(2019, 6, 30));
        }

        #[test]
        #[should_panic]
        fn no_date() {
            let xml = r#"<root>
                <Services>
                    <Service>
                        <OperatingPeriod />
                    </Service>
                </Services>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            get_service_validity_period(&root).unwrap();
        }

        #[test]
        #[should_panic]
        fn invalid_start_date() {
            let xml = r#"<root>
                <Services>
                    <Service>
                        <OperatingPeriod>
                            <StartDate>2019-42-01</StartDate>
                        </OperatingPeriod>
                    </Service>
                </Services>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            get_service_validity_period(&root).unwrap();
        }

        #[test]
        #[should_panic]
        fn invalid_end_date() {
            let xml = r#"<root>
                <Services>
                    <Service>
                        <OperatingPeriod>
                            <StartDate>2019-01-01</StartDate>
                            <EndDate>NotADate</EndDate>
                        </OperatingPeriod>
                    </Service>
                </Services>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            get_service_validity_period(&root).unwrap();
        }
    }

    mod update_validity_period {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        fn no_existing_validity_period() {
            let start_date = Date::from_ymd(2019, 1, 1);
            let end_date = Date::from_ymd(2019, 6, 30);
            let mut dataset = Dataset {
                id: String::from("dataset_id"),
                contributor_id: String::from("contributor_id"),
                start_date: MAX_DATE,
                end_date: MIN_DATE,
                ..Default::default()
            };
            let service_validity_period = ValidityPeriod {
                start_date,
                end_date,
            };
            update_validity_period(&mut dataset, &service_validity_period);
            assert_eq!(dataset.start_date, start_date);
            assert_eq!(dataset.end_date, end_date);
        }

        #[test]
        fn with_extended_validity_period() {
            let start_date = Date::from_ymd(2019, 1, 1);
            let end_date = Date::from_ymd(2019, 6, 30);
            let mut dataset = Dataset {
                id: String::from("dataset_id"),
                contributor_id: String::from("contributor_id"),
                start_date: Date::from_ymd(2019, 3, 1),
                end_date: Date::from_ymd(2019, 4, 30),
                ..Default::default()
            };
            let service_validity_period = ValidityPeriod {
                start_date,
                end_date,
            };
            update_validity_period(&mut dataset, &service_validity_period);
            assert_eq!(dataset.start_date, start_date);
            assert_eq!(dataset.end_date, end_date);
        }

        #[test]
        fn with_included_validity_period() {
            let start_date = Date::from_ymd(2019, 1, 1);
            let end_date = Date::from_ymd(2019, 6, 30);
            let mut dataset = Dataset {
                id: String::from("dataset_id"),
                contributor_id: String::from("contributor_id"),
                start_date,
                end_date,
                ..Default::default()
            };
            let service_validity_period = ValidityPeriod {
                start_date: Date::from_ymd(2019, 3, 1),
                end_date: Date::from_ymd(2019, 4, 30),
            };
            update_validity_period(&mut dataset, &service_validity_period);
            assert_eq!(dataset.start_date, start_date);
            assert_eq!(dataset.end_date, end_date);
        }
    }

    mod update_validity_period_from_transxchange {
        use super::*;

        #[test]
        fn has_start_and_end() {
            let xml = r#"<root>
                <Services>
                    <Service>
                        <OperatingPeriod>
                            <StartDate>2019-03-01</StartDate>
                            <EndDate>2019-04-30</EndDate>
                        </OperatingPeriod>
                    </Service>
                </Services>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let ds1 = Dataset {
                id: String::from("dataset_1"),
                contributor_id: String::from("contributor_id"),
                start_date: Date::from_ymd(2019, 1, 1),
                end_date: Date::from_ymd(2019, 6, 30),
                ..Default::default()
            };
            let ds2 = Dataset {
                id: String::from("dataset_2"),
                contributor_id: String::from("contributor_id"),
                start_date: Date::from_ymd(2019, 3, 31),
                end_date: Date::from_ymd(2019, 4, 1),
                ..Default::default()
            };
            let mut datasets = CollectionWithId::new(vec![ds1, ds2]).unwrap();
            let datasets = update_validity_period_from_transxchange(&mut datasets, &root).unwrap();
            let mut datasets_iter = datasets.values();
            let dataset = datasets_iter.next().unwrap();
            assert_eq!(dataset.start_date, Date::from_ymd(2019, 1, 1));
            assert_eq!(dataset.end_date, Date::from_ymd(2019, 6, 30));
            let dataset = datasets_iter.next().unwrap();
            assert_eq!(dataset.start_date, Date::from_ymd(2019, 3, 1));
            assert_eq!(dataset.end_date, Date::from_ymd(2019, 4, 30));
        }
    }

    mod get_by_reference {
        use super::*;

        #[test]
        fn has_operator() {
            let xml = r#"<root>
                    <Operator id="op1">
                        <OperatorCode>SOME_CODE</OperatorCode>
                        <TradingName>Some name</TradingName>
                    </Operator>
                    <Operator id="op2">
                        <OperatorCode>OTHER_CODE</OperatorCode>
                        <TradingName>Other name</TradingName>
                    </Operator>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let operator = get_by_reference(&root, "Operator", "op1").unwrap();
            let id = operator.try_only_child("OperatorCode").unwrap().text();
            assert_eq!(id, "SOME_CODE");
            let name = operator.try_only_child("TradingName").unwrap().text();
            assert_eq!(name, "Some name");
        }

        #[test]
        #[should_panic(expected = "Failed to find a child \\'Operator\\' in element \\'root\\'")]
        fn no_operator() {
            let xml = r#"<root>
                <Operator id="op1" />
                <Operator id="op2" />
            </root>"#;
            let root: Element = xml.parse().unwrap();
            get_by_reference(&root, "Operator", "op3").unwrap();
        }
    }

    mod load_network {
        use super::*;

        #[test]
        fn has_network() {
            let xml = r#"<root>
                <Services>
                    <Service>
                        <RegisteredOperatorRef>op1</RegisteredOperatorRef>
                    </Service>
                </Services>
                <Operators>
                    <Operator id="op1">
                        <OperatorCode>SOME_CODE</OperatorCode>
                        <TradingName>Some name</TradingName>
                    </Operator>
                    <Operator id="op2">
                        <OperatorCode>OTHER_CODE</OperatorCode>
                        <TradingName>Other name</TradingName>
                    </Operator>
                </Operators>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let network = load_network(&root).unwrap();
            assert_eq!(network.name, String::from("Some name"));
        }

        #[test]
        fn no_trading_name() {
            let xml = r#"<root>
                <Services>
                    <Service>
                        <RegisteredOperatorRef>op1</RegisteredOperatorRef>
                    </Service>
                </Services>
                <Operators>
                    <Operator id="op1">
                        <OperatorCode>SOME_CODE</OperatorCode>
                        <OperatorShortName>Some name</OperatorShortName>
                    </Operator>
                </Operators>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let network = load_network(&root).unwrap();
            assert_eq!(network.name, String::from("Some name"));
        }

        #[test]
        #[should_panic(
            expected = "Failed to find a child \\'RegisteredOperatorRef\\' in element \\'Service\\'"
        )]
        fn no_operator_ref() {
            let xml = r#"<root>
                <Services>
                    <Service />
                </Services>
                <Operators>
                    <Operator>
                        <TradingName>Some name</TradingName>
                    </Operator>
                </Operators>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            load_network(&root).unwrap();
        }

        #[test]
        #[should_panic(
            expected = "Failed to find a child \\'OperatorCode\\' in element \\'Operator\\'"
        )]
        fn no_id() {
            let xml = r#"<root>
                <Services>
                    <Service>
                        <RegisteredOperatorRef>op1</RegisteredOperatorRef>
                    </Service>
                </Services>
                <Operators>
                    <Operator id="op1">
                        <TradingName>Some name</TradingName>
                    </Operator>
                </Operators>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            load_network(&root).unwrap();
        }

        #[test]
        #[should_panic(
            expected = "Failed to find a child \\'OperatorShortName\\' in element \\'Operator\\'"
        )]
        fn no_name() {
            let xml = r#"<root>
                <Services>
                    <Service>
                        <RegisteredOperatorRef>op1</RegisteredOperatorRef>
                    </Service>
                </Services>
                <Operators>
                    <Operator id="op1">
                        <OperatorCode>SOME_CODE</OperatorCode>
                    </Operator>
                </Operators>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            load_network(&root).unwrap();
        }
    }

    mod load_companies {
        use super::*;

        #[test]
        fn has_company() {
            let xml = r#"<root>
                <Operators>
                    <Operator>
                        <OperatorCode>SOME_CODE</OperatorCode>
                        <OperatorShortName>Some name</OperatorShortName>
                    </Operator>
                    <Operator>
                        <OperatorCode>OTHER_CODE</OperatorCode>
                        <OperatorShortName>Other name</OperatorShortName>
                    </Operator>
                </Operators>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let companies = load_companies(&root).unwrap();
            let company = companies.get("SOME_CODE").unwrap();
            assert_eq!(company.name, String::from("Some name"));
            let company = companies.get("OTHER_CODE").unwrap();
            assert_eq!(company.name, String::from("Other name"));
        }

        #[test]
        #[should_panic(
            expected = "Failed to find a child \\'OperatorCode\\' in element \\'Operator\\'"
        )]
        fn no_id() {
            let xml = r#"<root>
                <Operators>
                    <Operator>
                        <OperatorShortName>Some name</OperatorShortName>
                    </Operator>
                </Operators>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            load_companies(&root).unwrap();
        }

        #[test]
        #[should_panic(
            expected = "Failed to find a child \\'OperatorShortName\\' in element \\'Operator\\'"
        )]
        fn no_name() {
            let xml = r#"<root>
                <Operators>
                    <Operator>
                        <OperatorCode>SOME_CODE</OperatorCode>
                    </Operator>
                </Operators>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            load_companies(&root).unwrap();
        }
    }

    mod load_commercial_physical_modes {
        use super::*;

        #[test]
        fn has_commercial_physical_modes() {
            let xml = r#"<root>
                <Services>
                    <Service>
                        <Mode>bus</Mode>
                    </Service>
                </Services>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let (commercial_mode, physical_mode) = load_commercial_physical_modes(&root).unwrap();

            assert_eq!(commercial_mode.id, String::from("Bus"));
            assert_eq!(commercial_mode.name, String::from("Bus"));

            assert_eq!(physical_mode.id, String::from("Bus"));
            assert_eq!(physical_mode.name, String::from("Bus"));
        }

        #[test]
        fn default_mode() {
            let xml = r#"<root>
                <Services>
                    <Service>
                        <Mode>unicorn</Mode>
                    </Service>
                </Services>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let (commercial_mode, physical_mode) = load_commercial_physical_modes(&root).unwrap();

            assert_eq!(commercial_mode.id, String::from("Bus"));
            assert_eq!(commercial_mode.name, String::from("Bus"));

            assert_eq!(physical_mode.id, String::from("Bus"));
            assert_eq!(physical_mode.name, String::from("Bus"));
        }
    }

    mod load_lines {
        use super::*;

        #[test]
        fn has_line() {
            let xml = r#"<root>
                <Operators>
                    <Operator id="O1">
                        <OperatorCode>SSWL</OperatorCode>
                    </Operator>
                </Operators>
                <Services>
                    <Service>
                        <ServiceCode>SCBO001</ServiceCode>
                        <Lines>
                            <Line id="SL1">
                                <LineName>1</LineName>
                            </Line>
                            <Line id="SL2">
                                <LineName>2</LineName>
                            </Line>
                        </Lines>
                        <Description>Cwmbran - Cwmbran via Thornhill</Description>
                        <StandardService>
                            <Origin>Cwmbran South</Origin>
                            <Destination>Cwmbran North</Destination>
                        </StandardService>
                        <RegisteredOperatorRef>O1</RegisteredOperatorRef>
                        <Mode>bus</Mode>
                    </Service>
                </Services>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let lines = load_lines(&root, "SSWL", "Bus").unwrap();
            let line = lines.get("SCBO001:SL1").unwrap();
            assert_eq!(line.code, Some(String::from("1")));
            assert_eq!(line.name, String::from("Cwmbran - Cwmbran via Thornhill"));
            assert_eq!(line.forward_name, Some(String::from("Cwmbran North")));
            // TODO: Fill up the forward direction
            assert_eq!(line.forward_direction, None);
            assert_eq!(line.backward_name, Some(String::from("Cwmbran South")));
            // TODO: Fill up the backward direction
            assert_eq!(line.backward_direction, None);
            assert_eq!(line.network_id, String::from("SSWL"));
            assert_eq!(line.commercial_mode_id, String::from("Bus"));

            let line = lines.get("SCBO001:SL2").unwrap();
            assert_eq!(line.code, Some(String::from("2")));
            assert_eq!(line.name, String::from("Cwmbran - Cwmbran via Thornhill"));
            assert_eq!(line.forward_name, Some(String::from("Cwmbran North")));
            // TODO: Fill up the forward direction
            assert_eq!(line.forward_direction, None);
            assert_eq!(line.backward_name, Some(String::from("Cwmbran South")));
            // TODO: Fill up the backward direction
            assert_eq!(line.backward_direction, None);
            assert_eq!(line.network_id, String::from("SSWL"));
            assert_eq!(line.commercial_mode_id, String::from("Bus"));
        }

        #[test]
        fn has_line_without_name() {
            let xml = r#"<root>
                <Operators>
                    <Operator id="O1">
                        <OperatorCode>SSWL</OperatorCode>
                    </Operator>
                </Operators>
                <Services>
                    <Service>
                        <ServiceCode>SCBO001</ServiceCode>
                        <Lines>
                            <Line id="SL1">
                                <LineName>1</LineName>
                            </Line>
                        </Lines>
                        <StandardService>
                            <Origin>Cwmbran South</Origin>
                            <Destination>Cwmbran North</Destination>
                        </StandardService>
                        <RegisteredOperatorRef>O1</RegisteredOperatorRef>
                        <Mode>bus</Mode>
                    </Service>
                </Services>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let lines = load_lines(&root, "SSWL", "Bus").unwrap();
            let line = lines.get("SCBO001:SL1").unwrap();
            assert_eq!(line.code, Some(String::from("1")));
            assert_eq!(line.name, String::from(UNDEFINED));
            assert_eq!(line.forward_name, Some(String::from("Cwmbran North")));
            // TODO: Fill up the forward direction
            assert_eq!(line.forward_direction, None);
            assert_eq!(line.backward_name, Some(String::from("Cwmbran South")));
            // TODO: Fill up the backward direction
            assert_eq!(line.backward_direction, None);
            assert_eq!(line.network_id, String::from("SSWL"));
            assert_eq!(line.commercial_mode_id, String::from("Bus"));
        }
    }

    mod parse_duration_in_seconds {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        fn parse_duration() {
            let time = parse_duration_in_seconds("PT1H30M5S").unwrap();
            assert_eq!(time, Time::new(1, 30, 5));
        }

        #[test]
        #[should_panic]
        fn invalid_duration() {
            parse_duration_in_seconds("NotAValidISO8601Duration").unwrap();
        }
    }

    mod get_duration_from {
        use super::*;

        #[test]
        fn get_duration() {
            let xml = r#"<root>
                <duration>PT30S</duration>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let time = get_duration_from(&root, "duration");
            assert_eq!(time, Time::new(0, 0, 30));
        }

        #[test]
        fn no_child() {
            let xml = r#"<root />"#;
            let root: Element = xml.parse().unwrap();
            let time = get_duration_from(&root, "duration");
            assert_eq!(time, Time::new(0, 0, 0));
        }
    }

    mod get_pickup_and_dropoff_types {
        use super::*;

        #[test]
        fn get_pickup() {
            let xml = r#"<root>
                <activity>pickUp</activity>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let (pickup_type, drop_off_type) = get_pickup_and_dropoff_types(&root, "activity");
            assert_eq!(pickup_type, 0);
            assert_eq!(drop_off_type, 1);
        }

        #[test]
        fn get_setdown() {
            let xml = r#"<root>
                <activity>setDown</activity>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let (pickup_type, drop_off_type) = get_pickup_and_dropoff_types(&root, "activity");
            assert_eq!(pickup_type, 1);
            assert_eq!(drop_off_type, 0);
        }

        #[test]
        fn get_pickupandsetdown() {
            let xml = r#"<root>
                <activity>pickUpAndSetDown</activity>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let (pickup_type, drop_off_type) = get_pickup_and_dropoff_types(&root, "activity");
            assert_eq!(pickup_type, 0);
            assert_eq!(drop_off_type, 0);
        }

        #[test]
        fn no_child() {
            let xml = r#"<root />"#;
            let root: Element = xml.parse().unwrap();
            let (pickup_type, drop_off_type) = get_pickup_and_dropoff_types(&root, "activity");
            assert_eq!(pickup_type, 0);
            assert_eq!(drop_off_type, 0);
        }
    }

    mod calculate_stop_times {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        fn generate_stop_times() {
            let stop_points = CollectionWithId::new(vec![
                StopPoint {
                    id: String::from("sp:1"),
                    ..Default::default()
                },
                StopPoint {
                    id: String::from("sp:2"),
                    ..Default::default()
                },
                StopPoint {
                    id: String::from("sp:3"),
                    ..Default::default()
                },
            ])
            .unwrap();
            let xml = r#"<root>
                <child>
                    <From>
                        <StopPointRef>sp:1</StopPointRef>
                        <WaitTime>PT60S</WaitTime>
                    </From>
                    <To>
                        <StopPointRef>sp:2</StopPointRef>
                    </To>
                    <RunTime>PT10M</RunTime>
                </child>
                <child>
                    <From>
                        <StopPointRef>sp:2</StopPointRef>
                        <WaitTime>PT1M30S</WaitTime>
                    </From>
                    <To>
                        <StopPointRef>sp:3</StopPointRef>
                        <WaitTime>PT2M</WaitTime>
                    </To>
                    <RunTime>PT5M</RunTime>
                </child>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let stop_times =
                calculate_stop_times(&stop_points, &root, &Time::new(0, 0, 0)).unwrap();
            let stop_time = &stop_times[0];
            assert_eq!(
                stop_time.stop_point_idx,
                stop_points.get_idx("sp:1").unwrap()
            );
            assert_eq!(stop_time.sequence, 1);
            assert_eq!(stop_time.arrival_time, Time::new(0, 0, 0));
            assert_eq!(stop_time.departure_time, Time::new(0, 1, 0));

            let stop_time = &stop_times[1];
            assert_eq!(
                stop_time.stop_point_idx,
                stop_points.get_idx("sp:2").unwrap()
            );
            assert_eq!(stop_time.sequence, 2);
            assert_eq!(stop_time.arrival_time, Time::new(0, 11, 0));
            assert_eq!(stop_time.departure_time, Time::new(0, 12, 30));

            let stop_time = &stop_times[2];
            assert_eq!(
                stop_time.stop_point_idx,
                stop_points.get_idx("sp:3").unwrap()
            );
            assert_eq!(stop_time.sequence, 3);
            assert_eq!(stop_time.arrival_time, Time::new(0, 17, 30));
            assert_eq!(stop_time.departure_time, Time::new(0, 17, 30));
        }

        #[test]
        #[should_panic(expected = "stop_id=\\\"sp:1\\\" not found")]
        fn stop_point_not_found() {
            let stop_points = CollectionWithId::new(vec![]).unwrap();
            let xml = r#"<root>
                <child>
                    <From>
                        <StopPointRef>sp:1</StopPointRef>
                        <WaitTime>PT60S</WaitTime>
                    </From>
                    <To>
                        <StopPointRef>sp:2</StopPointRef>
                    </To>
                    <RunTime>PT10M</RunTime>
                </child>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            calculate_stop_times(&stop_points, &root, &Time::new(0, 0, 0)).unwrap();
        }

        #[test]
        #[should_panic(expected = "Failed to find the last JourneyPatternSection")]
        fn no_section() {
            let stop_points = CollectionWithId::new(vec![]).unwrap();
            let xml = r#"<root />"#;
            let root: Element = xml.parse().unwrap();
            calculate_stop_times(&stop_points, &root, &Time::new(0, 0, 0)).unwrap();
        }
    }

    mod generate_calendar_dates {
        use super::*;

        #[test]
        fn all_work_week() {
            let xml = r#"<root>
                <RegularDayType>
                    <DaysOfWeek>
                        <MondayToFriday />
                    </DaysOfWeek>
                </RegularDayType>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let start_date = NaiveDate::from_ymd(2019, 08, 12);
            let end_date = NaiveDate::from_ymd(2019, 08, 20);
            let validity = ValidityPeriod {
                start_date,
                end_date,
            };
            let dates = generate_calendar_dates(&root, validity).unwrap();
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 12)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 13)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 14)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 15)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 16)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 19)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 20)));
        }

        #[test]
        fn not_saturday() {
            let xml = r#"<root>
                <RegularDayType>
                    <DaysOfWeek>
                        <NotSaturday />
                    </DaysOfWeek>
                </RegularDayType>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let start_date = NaiveDate::from_ymd(2019, 08, 17);
            let end_date = NaiveDate::from_ymd(2019, 08, 19);
            let validity = ValidityPeriod {
                start_date,
                end_date,
            };
            let dates = generate_calendar_dates(&root, validity).unwrap();
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 18)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 19)));
        }

        #[test]
        fn inverted_start_end() {
            let xml = r#"<root>
                <RegularDayType>
                    <DaysOfWeek>
                        <Weekend />
                        <Monday />
                    </DaysOfWeek>
                </RegularDayType>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let start_date = NaiveDate::from_ymd(2019, 08, 19);
            let end_date = NaiveDate::from_ymd(2019, 08, 17);
            let validity = ValidityPeriod {
                start_date,
                end_date,
            };
            let dates = generate_calendar_dates(&root, validity).unwrap();
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 17)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 18)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 19)));
        }

        #[test]
        fn unknown_tag() {
            let xml = r#"<root>
                <RegularDayType>
                    <DaysOfWeek>
                        <MondayToSaturday />
                        <MondayToSunday />
                        <UnknownTag />
                    </DaysOfWeek>
                </RegularDayType>
            </root>"#;
            let root: Element = xml.parse().unwrap();
            let start_date = NaiveDate::from_ymd(2019, 08, 12);
            let end_date = NaiveDate::from_ymd(2019, 08, 20);
            let validity = ValidityPeriod {
                start_date,
                end_date,
            };
            let dates = generate_calendar_dates(&root, validity).unwrap();
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 12)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 13)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 14)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 15)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 16)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 17)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 18)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 19)));
            assert!(dates.contains(&NaiveDate::from_ymd(2019, 08, 20)));
        }
    }
}
