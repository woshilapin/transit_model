// Copyright (C) 2017 Kisio Digital and/or its affiliates.
//
// This program is free software: you can redistribute it and/or modify it
// under the terms of the GNU Affero General Public License as published by the
// Free Software Foundation, version 3.

// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
// FOR A PARTICULAR PURPOSE. See the GNU Affero General Public License for more
// details.

// You should have received a copy of the GNU Affero General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>

// This module is an implementation of the algorithm described in
// https://github.com/CanalTP/navitia/blob/dev/documentation/rfc/sorting_vehicles_route_schedules.md

use crate::objects::{StopPoint, Time, VehicleJourney};
use std::{
    cmp::{Ordering, PartialOrd},
    collections::{BinaryHeap, HashMap},
};
use transit_model_collection::Idx;

// Each voter is materialized by a StopPoint
type Voter = Idx<StopPoint>;
// The voter votes for a candidate which is a VehicleJourney
type Candidate<'m> = &'m String;
// Each voter (StopPoint) votes for the candidates (VehicleJourney) by ordering
// them by priority of their `departure_time`.
type Votes<'m> = HashMap<Voter, BinaryHeap<OrderedCandidate<'m>>>;
// Result of the votes summarize in a matrix:
// - the key is the oriented relation between 2 candidates
// - the value is the number of received votes
type VoteMatrix<'m> = HashMap<(Candidate<'m>, Candidate<'m>), u32>;
// A ballot is the expression of a voter (StopPoint) about a candidate (VehicleJourney)
// In order to express a meaningful vote on a VehicleJourney, a StopPoint needs
// to remember at which time this VehicleJourney pass at the StopPoint. Therefore, the ballot is the combination of:
// - the voter (`Idx<StopPoint>`)
// - the candidate (the `id` of the VehicleJourney, a `&String`)
// - the time of passage (`Time`)
type Ballot<'m> = (Idx<StopPoint>, &'m String, Time);

// This is a wrapper around a candidate which include the passing time. This
// will allow to automatically order the candidate per voter in a `BinaryHeap`
// (see type `Votes` above).
#[derive(Debug)]
struct OrderedCandidate<'m> {
    candidate: Candidate<'m>,
    time: Time,
}

impl PartialEq for OrderedCandidate<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.time.eq(&other.time)
    }
}

impl Eq for OrderedCandidate<'_> {}

// The order needs to be reverse because smaller Time needs to have bigger
// priority (see how BinaryHeap works)
impl PartialOrd for OrderedCandidate<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.time.partial_cmp(&other.time).map(Ordering::reverse)
    }
}

// The order needs to be reverse because smaller Time needs to have bigger
// priority (see how BinaryHeap works)
impl Ord for OrderedCandidate<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.time.cmp(&other.time).reverse()
    }
}

// VoteRelation express the relation between 2 candidates and the number of
// voters that agree with this ordering
#[derive(Debug)]
struct VoteRelation<'m> {
    winner: Candidate<'m>,
    loser: Candidate<'m>,
    votes: u32,
}

fn process_ballots<'m, I>(ballots: I) -> Votes<'m>
where
    I: Iterator<Item = Ballot<'m>>,
{
    ballots.fold(Votes::default(), |mut votes, (voter, candidate, time)| {
        votes
            .entry(voter)
            .or_insert_with(BinaryHeap::new)
            .push(OrderedCandidate { candidate, time });
        votes
    })
}

fn build_combinations(mut candidates: BinaryHeap<OrderedCandidate>) -> Vec<VoteRelation> {
    let mut vote_relations = Vec::new();
    while let Some(candidate) = candidates.pop() {
        let winner = candidate.candidate;
        for OrderedCandidate {
            candidate: loser, ..
        } in &candidates
        {
            vote_relations.push(VoteRelation {
                winner,
                loser,
                votes: 1,
            });
        }
    }
    vote_relations
}

fn votes_summary_table<'m>(mut votes: Votes<'m>) -> VoteMatrix<'m> {
    votes
        .drain()
        .map(|(_, candidates)| candidates)
        .flat_map(|candidates| build_combinations(candidates))
        .fold(VoteMatrix::default(), |mut vote_matrix, vote_relation| {
            dbg!(&vote_relation);
            let votes = vote_matrix
                .entry((vote_relation.winner, vote_relation.loser))
                .or_insert(0);
            *votes += vote_relation.votes;
            vote_matrix
        })
}

pub fn build_stop_sequence<'m, I>(vehicle_journeys: I) -> Vec<Idx<StopPoint>>
where
    I: IntoIterator<Item = &'m VehicleJourney>,
{
    let ballots = vehicle_journeys.into_iter().flat_map(|vehicle_journey| {
        vehicle_journey.stop_times.iter().map(move |stop_time| {
            (
                stop_time.stop_point_idx,
                &vehicle_journey.id,
                stop_time.departure_time,
            )
        })
    });
    let votes = process_ballots(ballots);
    let _summary_table = votes_summary_table(votes);
    // # Write a 'compress_summary_table'
    // The summary table contains all votes per relation. The problem is that
    // there is votes for A compared to B but also for B compared to A.
    // We can compress the table by keeping only the difference of votes between
    // the A->B and B->A (we keep the positive one).
    //
    // # Inserting edges
    // We can insert edges into our graph by maintaining a list of accessible
    // childrens at the same time. This will allow us to detect cycle. With
    // these childrens, we also keep the number of hops to acceed these
    // childrens: this will help later to find the longest path.
    //
    // WARNING: It might be better to keep a list of all accessible predecessors
    // instead of the childrens. It would simplify the completion of all the
    // accessible predecessors when adding a new edge (just add all the
    // predecessors of the new node you add to the new other node you add).
    //
    // Reminder: we insert the edges in the order of their number of votes. What
    // do we do in case of equality?
    //
    // Example:
    // We have the 3 following edges to insert:
    // - C > A (3 votes)
    // - A > B (2 votes)
    // - B > C (1 vote)
    // We start with a list of accessible childrens empty for A, B and C.
    // { A: {}, B: {}, C: {} }
    // We insert the first edge C > A.
    // Now, A becomes accessible from C in 1 hop so our lists of accessible
    // childrens becomes:
    // { A: {}, B: {}, C: { A:1 } }
    // Now we insert A > B.
    // Inserting means B becomes accessible from A.
    // { A: { B:1 }, B: {}, C: { A:1 } }
    // This means that now B is accessible from C with 2 hops
    // { A: { B:1 }, B: {}, C: { A:1, B:2 } }
    // Finally we insert B > C.
    // Inserting means C becomes accessible from B.
    // { A: { B:1 }, B: { C:1 }, C: { A:1, B:2 } }
    // We deduce that now B can access A though C, and then can access B through
    // A: B can access B, we have a cycle.
    // We need to rollback the insertion of edge B > C: this edge cannot be
    // inserted without introducing a cycle.
    //
    // # Finding the source
    // In the list of all the accessible childrens, we need to find the one that
    // have the longest list. This is the one that can access all the other
    // nodes.  The other nodes can access at maximum all the other nodes minus
    // the source so their list should be shorter.
    // We assume that we don't create 2 disconnected graphs because that would
    // mean we have 2 VehicleJourney that don't share any StopPoint in the same
    // Route.
    //
    // # Build the ordered list of VehicleJourney
    // From the source's node, we go forward to all the nodes that are
    // accessible with 1 hop. When there is only one accessible node, it can be
    // inserted in our final list of VehicleJourney.
    // When 2 (or more) childrens are accessible in 1 hop, we need to which one
    // is going to be chosen in priority. These 2 nodes have also a list of
    // accessible childrens (with a distance). We need to find the node which
    // has the longest path available (the children with the longest distance).
    //
    // WARNING: It might be more interesting to have a simple list of direct
    // accessible childrens and browse the multiple possibilities (in case of
    // equality) as we go down the graph.
    Vec::new()
}

#[cfg(test)]
mod tests {
    use super::*;
    use transit_model_collection::CollectionWithId;

    fn stop_points() -> CollectionWithId<StopPoint> {
        CollectionWithId::new(vec![
            StopPoint {
                id: String::from("stop_point_1"),
                ..Default::default()
            },
            StopPoint {
                id: String::from("stop_point_2"),
                ..Default::default()
            },
            StopPoint {
                id: String::from("stop_point_3"),
                ..Default::default()
            },
            StopPoint {
                id: String::from("stop_point_4"),
                ..Default::default()
            },
            StopPoint {
                id: String::from("stop_point_5"),
                ..Default::default()
            },
            StopPoint {
                id: String::from("stop_point_6"),
                ..Default::default()
            },
            StopPoint {
                id: String::from("stop_point_7"),
                ..Default::default()
            },
            StopPoint {
                id: String::from("stop_point_8"),
                ..Default::default()
            },
        ])
        .unwrap()
    }

    mod process_ballots {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        fn two_ballots_same_voter() {
            let stop_points = stop_points();
            let stop_point_1_idx = stop_points.get_idx("stop_point_1").unwrap();
            let vehicle_journey_1_id = String::from("vehicle_journey_1");
            let vehicle_journey_2_id = String::from("vehicle_journey_2");
            let ballots = vec![
                (stop_point_1_idx, &vehicle_journey_1_id, Time::new(0, 0, 0)),
                (stop_point_1_idx, &vehicle_journey_2_id, Time::new(1, 0, 0)),
            ];

            let votes = process_ballots(ballots.into_iter());

            assert_eq!(1, votes.len());
            let candidates = votes.get(&stop_point_1_idx).unwrap();
            assert_eq!(2, candidates.len());
            let mut candidates = candidates.into_iter();

            let candidate = candidates.next().unwrap();
            assert_eq!("vehicle_journey_1", candidate.candidate);
            assert_eq!(Time::new(0, 0, 0), candidate.time);

            let candidate = candidates.next().unwrap();
            assert_eq!("vehicle_journey_2", candidate.candidate);
            assert_eq!(Time::new(1, 0, 0), candidate.time);
        }
    }

    mod build_combinations {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        fn no_candidate_gives_no_relation() {
            let candidates = BinaryHeap::default();
            let vote_relations = build_combinations(candidates);
            assert_eq!(0, vote_relations.len());
        }

        #[test]
        fn one_candidate_gives_no_relation() {
            let mut candidates = BinaryHeap::default();
            let vehicle_journey_id = String::from("vehicle_journey_id");
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_id,
                time: Time::new(0, 0, 0),
            });
            let vote_relations = build_combinations(candidates);
            assert_eq!(0, vote_relations.len());
        }

        #[test]
        fn all_possible_relations() {
            let mut candidates = BinaryHeap::default();
            let vehicle_journey_1_id = String::from("vehicle_journey_1");
            let vehicle_journey_2_id = String::from("vehicle_journey_2");
            let vehicle_journey_3_id = String::from("vehicle_journey_3");
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_1_id,
                time: Time::new(0, 0, 0),
            });
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_2_id,
                time: Time::new(1, 0, 0),
            });
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_3_id,
                time: Time::new(2, 0, 0),
            });
            let vote_relations = build_combinations(candidates);
            assert_eq!(3, vote_relations.len());

            let vote_relation = &vote_relations[0];
            assert_eq!("vehicle_journey_1", vote_relation.winner);
            assert_eq!("vehicle_journey_2", vote_relation.loser);
            assert_eq!(1, vote_relation.votes);

            let vote_relation = &vote_relations[1];
            assert_eq!("vehicle_journey_1", vote_relation.winner);
            assert_eq!("vehicle_journey_3", vote_relation.loser);
            assert_eq!(1, vote_relation.votes);

            let vote_relation = &vote_relations[2];
            assert_eq!("vehicle_journey_2", vote_relation.winner);
            assert_eq!("vehicle_journey_3", vote_relation.loser);
            assert_eq!(1, vote_relation.votes);
        }
    }

    mod votes_summary_table {
        use super::*;
        use pretty_assertions::assert_eq;

        // This test is the example from the documentation at
        // https://github.com/CanalTP/navitia/blob/dev/documentation/rfc/sorting_vehicles_route_schedules.md#issue
        #[test]
        fn summary_table_for_abc() {
            let stop_points = stop_points();
            let stop_point_1_idx = stop_points.get_idx("stop_point_1").unwrap();
            let stop_point_2_idx = stop_points.get_idx("stop_point_2").unwrap();
            let stop_point_3_idx = stop_points.get_idx("stop_point_3").unwrap();
            let stop_point_4_idx = stop_points.get_idx("stop_point_4").unwrap();
            let stop_point_5_idx = stop_points.get_idx("stop_point_5").unwrap();
            let stop_point_6_idx = stop_points.get_idx("stop_point_6").unwrap();
            let stop_point_7_idx = stop_points.get_idx("stop_point_7").unwrap();
            let stop_point_8_idx = stop_points.get_idx("stop_point_8").unwrap();
            let vehicle_journey_a = String::from("vehicle_journey_a");
            let vehicle_journey_b = String::from("vehicle_journey_b");
            let vehicle_journey_c = String::from("vehicle_journey_c");
            let mut votes = Votes::default();
            let mut candidates = BinaryHeap::default();
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_a,
                time: Time::new(1, 0, 0),
            });
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_b,
                time: Time::new(2, 0, 0),
            });
            votes.insert(stop_point_1_idx, candidates);
            let mut candidates = BinaryHeap::default();
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_a,
                time: Time::new(2, 0, 0),
            });
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_b,
                time: Time::new(3, 0, 0),
            });
            votes.insert(stop_point_2_idx, candidates);
            let mut candidates = BinaryHeap::default();
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_a,
                time: Time::new(3, 0, 0),
            });
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_b,
                time: Time::new(4, 0, 0),
            });
            votes.insert(stop_point_3_idx, candidates);
            let mut candidates = BinaryHeap::default();
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_a,
                time: Time::new(5, 0, 0),
            });
            votes.insert(stop_point_4_idx, candidates);
            let mut candidates = BinaryHeap::default();
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_a,
                time: Time::new(7, 0, 0),
            });
            votes.insert(stop_point_5_idx, candidates);
            let mut candidates = BinaryHeap::default();
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_a,
                time: Time::new(9, 0, 0),
            });
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_b,
                time: Time::new(7, 0, 0),
            });
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_c,
                time: Time::new(8, 0, 0),
            });
            votes.insert(stop_point_6_idx, candidates);
            let mut candidates = BinaryHeap::default();
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_a,
                time: Time::new(10, 0, 0),
            });
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_c,
                time: Time::new(9, 0, 0),
            });
            votes.insert(stop_point_7_idx, candidates);
            let mut candidates = BinaryHeap::default();
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_a,
                time: Time::new(11, 0, 0),
            });
            candidates.push(OrderedCandidate {
                candidate: &vehicle_journey_c,
                time: Time::new(10, 0, 0),
            });
            votes.insert(stop_point_8_idx, candidates);

            dbg!(&votes);
            let summary_table = votes_summary_table(votes);
            dbg!(&summary_table);

            let a_to_b_score = summary_table
                .get(&(&vehicle_journey_a, &vehicle_journey_b))
                .unwrap();
            assert_eq!(3, *a_to_b_score);
            let b_to_a_score = summary_table
                .get(&(&vehicle_journey_b, &vehicle_journey_a))
                .unwrap();
            assert_eq!(1, *b_to_a_score);
            let b_to_c_score = summary_table
                .get(&(&vehicle_journey_b, &vehicle_journey_c))
                .unwrap();
            assert_eq!(1, *b_to_c_score);
            let c_to_a_score = summary_table
                .get(&(&vehicle_journey_c, &vehicle_journey_a))
                .unwrap();
            assert_eq!(3, *c_to_a_score);
        }
    }

    mod build_stop_sequence {
        use super::*;
        use crate::objects::{CommentLinksT, KeysValues, StopTime};
        use pretty_assertions::assert_eq;

        fn stop_time(
            stop_point_idx: Idx<StopPoint>,
            sequence: u32,
            departure_time: Time,
        ) -> StopTime {
            StopTime {
                stop_point_idx,
                sequence,
                arrival_time: Time::new(0, 0, 0),
                departure_time,
                boarding_duration: 0,
                alighting_duration: 0,
                pickup_type: 0,
                drop_off_type: 0,
                datetime_estimated: false,
                local_zone_id: None,
                precision: None,
            }
        }

        fn vehicle_journey(id: String, stop_times: Vec<StopTime>) -> VehicleJourney {
            VehicleJourney {
                id,
                codes: KeysValues::default(),
                object_properties: KeysValues::default(),
                comment_links: CommentLinksT::default(),
                route_id: String::from("route_id"),
                physical_mode_id: String::from("Bus"),
                dataset_id: String::from("dataset_id"),
                service_id: String::from("service_id"),
                headsign: None,
                short_name: None,
                block_id: None,
                company_id: String::from("company_id"),
                trip_property_id: None,
                geometry_id: None,
                stop_times,
                journey_pattern_id: None,
            }
        }

        // Use case:
        // The two vehicle journeys have the same journey pattern.
        //
        // Expected result:
        // The order of stop points must be the same as either of the vehicle
        // journey.
        #[test]
        fn same_journey_pattern() {
            let stop_points = stop_points();
            let stop_time_1 = stop_time(
                stop_points.get_idx("stop_point_1").unwrap(),
                0,
                Time::new(1, 0, 0),
            );
            let stop_time_2 = stop_time(
                stop_points.get_idx("stop_point_2").unwrap(),
                0,
                Time::new(2, 0, 0),
            );
            let stop_time_3 = stop_time(
                stop_points.get_idx("stop_point_3").unwrap(),
                0,
                Time::new(3, 0, 0),
            );
            let vehicle_journey_1 = vehicle_journey(
                String::from("vehicle_journey_1"),
                vec![
                    stop_time_1.clone(),
                    stop_time_2.clone(),
                    stop_time_3.clone(),
                ],
            );
            let vehicle_journey_2 = vehicle_journey(
                String::from("vehicle_journey_2"),
                vec![
                    stop_time_1.clone(),
                    stop_time_2.clone(),
                    stop_time_3.clone(),
                ],
            );
            let vehicle_journeys = vec![vehicle_journey_1, vehicle_journey_2];
            let route_points = build_stop_sequence(vehicle_journeys.iter());
            assert_eq!(3, route_points.len());
            let stop_point = &stop_points[route_points[0]];
            assert_eq!("stop_point_1", stop_point.id.as_str());
            let stop_point = &stop_points[route_points[1]];
            assert_eq!("stop_point_2", stop_point.id.as_str());
            let stop_point = &stop_points[route_points[2]];
            assert_eq!("stop_point_3", stop_point.id.as_str());
        }

        // Use case:
        // The two vehicle journey starts from different stop points.
        //
        // Expected result:
        // The two stop points must be ordered by their departure_time
        #[test]
        fn forked_journey_pattern() {
            let stop_points = stop_points();
            let stop_time_1 = stop_time(
                stop_points.get_idx("stop_point_1").unwrap(),
                0,
                Time::new(1, 0, 0),
            );
            let stop_time_2 = stop_time(
                stop_points.get_idx("stop_point_2").unwrap(),
                0,
                Time::new(2, 0, 0),
            );
            let stop_time_3 = stop_time(
                stop_points.get_idx("stop_point_3").unwrap(),
                0,
                Time::new(3, 0, 0),
            );
            let stop_time_4 = stop_time(
                stop_points.get_idx("stop_point_4").unwrap(),
                0,
                Time::new(4, 0, 0),
            );
            let stop_time_5 = stop_time(
                stop_points.get_idx("stop_point_5").unwrap(),
                0,
                Time::new(5, 0, 0),
            );
            let vehicle_journey_1 = vehicle_journey(
                String::from("vehicle_journey_1"),
                vec![
                    stop_time_1.clone(),
                    stop_time_3.clone(),
                    stop_time_4.clone(),
                ],
            );
            let vehicle_journey_2 = vehicle_journey(
                String::from("vehicle_journey_2"),
                vec![
                    stop_time_2.clone(),
                    stop_time_3.clone(),
                    stop_time_5.clone(),
                ],
            );
            let vehicle_journeys = vec![vehicle_journey_1, vehicle_journey_2];
            let route_points = build_stop_sequence(vehicle_journeys.iter());
            assert_eq!(5, route_points.len());
            let stop_point = &stop_points[route_points[0]];
            assert_eq!("stop_point_1", stop_point.id.as_str());
            let stop_point = &stop_points[route_points[1]];
            assert_eq!("stop_point_2", stop_point.id.as_str());
            let stop_point = &stop_points[route_points[2]];
            assert_eq!("stop_point_3", stop_point.id.as_str());
            let stop_point = &stop_points[route_points[3]];
            assert_eq!("stop_point_4", stop_point.id.as_str());
            let stop_point = &stop_points[route_points[4]];
            assert_eq!("stop_point_5", stop_point.id.as_str());
        }

        // Use case:
        // The two vehicle journeys have the same first and last stop point but
        // their middle stop point differ.
        //
        // Expected result:
        // The two middle stop points must be ordered by their departure time.
        #[test]
        fn in_between_stop() {
            let stop_points = stop_points();
            let stop_time_1 = stop_time(
                stop_points.get_idx("stop_point_1").unwrap(),
                0,
                Time::new(1, 0, 0),
            );
            let stop_time_2 = stop_time(
                stop_points.get_idx("stop_point_2").unwrap(),
                0,
                Time::new(2, 0, 0),
            );
            let stop_time_3 = stop_time(
                stop_points.get_idx("stop_point_3").unwrap(),
                0,
                Time::new(3, 0, 0),
            );
            let stop_time_4 = stop_time(
                stop_points.get_idx("stop_point_4").unwrap(),
                0,
                Time::new(4, 0, 0),
            );
            let vehicle_journey_1 = vehicle_journey(
                String::from("vehicle_journey_1"),
                vec![
                    stop_time_1.clone(),
                    stop_time_3.clone(),
                    stop_time_4.clone(),
                ],
            );
            let vehicle_journey_2 = vehicle_journey(
                String::from("vehicle_journey_2"),
                vec![
                    stop_time_1.clone(),
                    stop_time_2.clone(),
                    stop_time_4.clone(),
                ],
            );
            let vehicle_journeys = vec![vehicle_journey_1, vehicle_journey_2];
            let route_points = build_stop_sequence(vehicle_journeys.iter());
            assert_eq!(4, route_points.len());
            let stop_point = &stop_points[route_points[0]];
            assert_eq!("stop_point_1", stop_point.id.as_str());
            let stop_point = &stop_points[route_points[1]];
            assert_eq!("stop_point_2", stop_point.id.as_str());
            let stop_point = &stop_points[route_points[2]];
            assert_eq!("stop_point_3", stop_point.id.as_str());
            let stop_point = &stop_points[route_points[3]];
            assert_eq!("stop_point_4", stop_point.id.as_str());
        }
    }
}
