/**** Best Bike Paths model for alloy specification ****/

/** For readability and simplicity motivations we decided to not completely
	use every possible object of the model (Nodes are modeled without 
	coordinates data and so equality is by object, not value).**/

/** For modelling purposes, segments are different even if not (imagine a
	map-like interaction with common nodes **/

/**** Variable stuff ****
Segment: 			status
Path: 				score, start
Trip: 				path, averageSpeed, duration, externalStats
RegisteredUser:	registeredTrips, publishedTrips **/

/*** SIGNATURES ***/
open util/ordering[World]
abstract sig Status{}
one sig Clear extends Status{}
one sig RoadWork extends Status{}
one sig Pothole extends Status{}

sig Segment{
	nextSegment: lone Segment,
}

sig Path{}

sig Statistics{}

sig Trip{}

sig RegisteredUser {}

/**** FSM ****/
abstract sig ManualInsertionState{
	next: lone ManualInsertionState
}
one sig StartTripCreation extends ManualInsertionState{}
one sig FirstSegmentCreation extends ManualInsertionState{}
one sig SegmentInsertion extends ManualInsertionState{}
one sig ComputeScore extends ManualInsertionState{}
one sig InsertDuration extends ManualInsertionState{}
one sig ComputeStatistics extends ManualInsertionState{}
one sig PublicPrivate extends ManualInsertionState{}

/**** WORLD OBJECT ****/
sig World{
	state: one ManualInsertionState,

	registeredTrips: RegisteredUser -> set Trip,
	publishedTrips: RegisteredUser -> set Trip,
	
	pathOf: Trip -> lone Path,
	avgSpeedOf: Trip -> lone Statistics,
	durationOf: Trip -> lone Statistics,
	externalStatsOf: Trip -> lone Statistics,

	startOf: Path -> lone Segment,
	scoreOf: Path -> lone Int
}

fact MultipleWorlds{
	some World
}

/*** FACTS ***/
fact pathsLinkedToTrips{
	all w: World|(
		all p: Path|(
			some t: Trip| ((t->p) in w.pathOf)
		)
	)
}

fact statsLinkedToTrips{
	all w: World|(
		all s: Statistics|(
			some t: Trip| (
				(t->s) in w.avgSpeedOf or
				(t->s) in w.durationOf or
				(t->s) in w.externalStatsOf
			)
		)
	)
}

fact publishedTripsIsSubset{
	all w: World|(
		all u: RegisteredUser|(
			w.publishedTrips[u] in w.registeredTrips[u]
		)
	)
}

fact insertionOrder{
	StartTripCreation.next = FirstSegmentCreation
	FirstSegmentCreation.next = SegmentInsertion
	SegmentInsertion.next = ComputeScore
	ComputeScore.next = InsertDuration
	InsertDuration.next = ComputeStatistics
	ComputeStatistics.next = PublicPrivate
	PublicPrivate.next = PublicPrivate
}

/*** PREDICATES ***/
pred startTripTransition {
	all w: World - last |
    	let w2 = w.next | (
      		(w.state = StartTripCreation) implies (
        	some u: RegisteredUser, t: Trip, p: Path |
          	// u gains trip t in the next world (and t wasn't present in u's trips in w)
          	t in w2.registeredTrips[u] and not (t in w.registeredTrips[u])
          	// t gets its path set to p in w2
          	and (t->p) in w2.pathOf and not ((t->p) in w.pathOf)
          	// t's statistics are empty in the next world
          	and no w2.avgSpeedOf[t] and no w2.durationOf[t] and no w2.externalStatsOf[t]
          	// Everything else remains unchanged across worlds except the intended changes:
          	and all otherUser: RegisteredUser - u |
             	w2.registeredTrips[otherUser] = w.registeredTrips[otherUser]
          	// trips other than t keep the same path mapping
          	and all tp: Trip - t |
             	w.pathOf[tp] = w2.pathOf[tp]
          	// path/segment structure unchanged
          	and all pth: Path | w2.startOf[pth] = w.startOf[pth]
      	)
    )
}



fact segmentsFacts{

	// Segments are saved only if associated with another 
	// segment or a Path (and at least an object Path 
	// is needed in the chain)
	all w: World| (
		all s: Segment| (
			some ss: Segment|( 
				ss.nextSegment = s or 
				some p: Path|(p->s) in w.startOf
			)
		)
	)

	all w: World|(
		all s: Segment|(
			// if segment is last in chain or in a cycle
			(s.nextSegment = none or s in s.^nextSegment) implies 
			// then from said segment i can walk backwards 
			// until i find a path's start
			some p: Path|(
				w.startOf[p] in s.^~nextSegment
			)
		)
	)
}

fact equalPaths{
	// Paths are equal if the segments inside 
	// are the same sequence of objects
	all p1,p2: Path|(
		p1 != p2 implies (
			all w: World|(
				w.startOf[p1].*nextSegment != w.startOf[p2].*nextSegment
			)
		)
	)
}

pred manualInsertionExample {
  // require there is at least one world pair to exercise a step
  some w: World | w.next != none
  // force that first transition satisfy the startTripTransition properties
  startTripTransition
}

run manualInsertionExample for 3 World, 4 RegisteredUser, 6 Trip, 4 Path, 8 Segment, 3 Statistics, 5 Int


/**for 50 but 
		exactly 2 RegisteredUser,
		exactly 10 Trip,
		exactly 5 Path,
		exactly 30 Segment
**/
