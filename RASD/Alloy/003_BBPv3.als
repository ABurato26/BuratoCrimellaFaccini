/**** Best Bike Paths model for alloy specification ****/
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

fact WorldSequence{
	// first ever state is first of the FSM
	first.state = StartTripCreation

	// transitions are always in FSM order
	all w: World - last|
		w.next.state = w.state or w.next.state = w.state.next
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
	all w: World - last |(
      	(w.state = StartTripCreation) implies (
        	some u: RegisteredUser, t: Trip, p: Path |(
         		// u gains trip t in the next world 
          		t in w.next.registeredTrips[u] 
				
				// t wasn't present in u's trips in w
				and not (t in w.registeredTrips[u])
          		
				// t gets its path set to p in w.next
         		and (t->p) in w.next.pathOf and not ((t->p) in w.pathOf)

          		// t's statistics are empty in the next world
          		and no w.next.avgSpeedOf[t] 
				and no w.next.durationOf[t] 
				and no w.next.externalStatsOf[t]
		
          		// Everything else remains unchanged
          		and all otherUser: RegisteredUser - u |(
            		w.next.registeredTrips[otherUser] = 
					w.registeredTrips[otherUser]
					and w.next.publishedTrips[otherUser] =
					w.publishedTrips[otherUser]
				)

          		// trips other than t keep the same path mapping
          		and all tp: Trip - t |(
            		w.pathOf[tp] = w.next.pathOf[tp]
				)

          		// path/segment structure unchanged
          		and all pth: Path | (
					w.next.startOf[pth] = w.startOf[pth]
				)
			)
		)
		
		and (w.state = FirstSegmentCreation) implies(
			some u: RegisteredUser, p: Path|(
				one s: Segment|(
					s in w.next.startOf[p] 
					and p in w.next.pathOf[w.next.publishedTrips[u]]
				)
				
				//and all otherUser: RegisteredUser - u|(	
			)
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

run manualInsertionExample for 
	5 World, 
	exactly 1 RegisteredUser, 
	exactly 2 Trip, 
	1 Path, 
	8 Segment, 
	3 Statistics, 
	5 Int

/**for 50 but 
		exactly 2 RegisteredUser,
		exactly 10 Trip,
		exactly 5 Path,
		exactly 30 Segment
**/
