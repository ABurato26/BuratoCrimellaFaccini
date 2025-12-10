/**** Best Bike Paths model for alloy specification ****/

/** For readability and simplicity motivations we decided to not completely
	use every possible object of the model (Nodes are modeled without 
	coordinates data and so equality is by object, not value).**/

/** For modelling purposes, segments are different even if not (imagine a
	map-like interaction with common nodes **/

/**** Variable stuff ****
Segment: 			status
Path: 				score
Trip: 				path, averageSpeed, duration, externalStats
RegisteredUser:	registeredTrips, publishedTrips **/

/*** SIGNATURES ***/
abstract sig Status{}
one sig Clear extends Status{}
one sig RoadWork extends Status{}
one sig Pothole extends Status{}

sig Segment{
	nextSegment: lone Segment,
	var status: some Status
}

sig Path{
	start: Segment,
	var score: Int
}

sig Statistics{}

sig Trip{
	var path: lone Path,
	var averageSpeed: lone Statistics,
	var duration: lone Statistics,
	var externalStats: lone Statistics
}

sig RegisteredUser {
	var registeredTrips: set Trip,
	var publishedTrips: set Trip
}{
	// published trips are a subset of all registered trips
	publishedTrips in registeredTrips 
}

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

one sig CurrentState{
	var state: one ManualInsertionState
}{
	state' in state + state.next
}

/*** FACTS ***/

/**
fact default{
	all s: Segment| s.nextSegment' = s.nextSegment and
		s.status' = s.status

	and all t: Trip |( 
		t.(path + averageSpeed + duration + externalStats)' = 
		t.(path + averageSpeed + duration + externalStats))
	
	and all p: Path| p.start' = p.start and
		p.score' = p.score

	and all ru: RegisteredUser|
		ru.(registeredTrips + publishedTrips)' = 
		ru.(registeredTrips + publishedTrips)

	and all s: Segment| (s.nextSegment' != s)

	and all s: Segment| ((Clear in s.status') implies #s.status' = 1)
}
**/

fact alwaysValid{
	// Paths are saved only if associated with 
	// at least a Trip
	all p: Path|(
		some t: Trip| t.path = p)

	and 
	// Statistics are saved only if associated 
	// with at least a trip
	all s: Statistics|(
		some t: Trip| t.averageSpeed = s 
		or t.duration = s 
		or t.externalStats = s)

	and
	// statistics are different in trips
	all t: Trip|(
		t.averageSpeed != t.duration and t.duration != t.externalStats)
		/**
		// Trips are saved only if associated with 
		// at least a registered user
		and one u: RegisteredUser| t in u.registeredTrips
		**/
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
pred updateOnlyUser[u: RegisteredUser]{
	// state is not changed by the predicate itself
	CurrentState.state' in CurrentState.state + CurrentState.state.next

	// Start trip creation
	(CurrentState.state = StartTripCreation) implies(
		// only the added trip changes
		one t: Trip, p: Path|( 
			// new trip is added
			u.registeredTrips' = u.registeredTrips + t 
			and t not in u.registeredTrips
			and t.path' = p 
			and p.start = none
			and t.averageSpeed' = none
			and t.duration' = none
			and t.externalStats' = none
			and all tr: Trip - t|(
				tr.(path + averageSpeed + duration + externalStats)' = 
				tr.(path + averageSpeed + duration + externalStats)
			)
		)
		and
		all s: Segment| (s.nextSegment' = s.nextSegment and
			s.status' = s.status)
	
		and all p: Path| (p.start' = p.start and
			p.score' = p.score)

		and all ru: RegisteredUser - u|(
			ru.(registeredTrips + publishedTrips)' = 
			ru.(registeredTrips + publishedTrips))

		and all s: Segment| (s.nextSegment' != s)

		and all s: Segment| ((Clear in s.status') implies #s.status' = 1)
	)
	(CurrentState.state = FirstSegmentCreation) implies (
		one s: Segment|(
			// new segment is added
			some t: Trip| some p: Path| t.path' = p and p.start' = s
		)
		
	)
/**
	(CurrentState.state = SegmentInsertion) implies ()
	(CurrentState.state = ComputeScore) implies ()
	(CurrentState.state = InsertDuration) implies ()
	(CurrentState.state = ComputeStatistics) implies ()
	(CurrentState.state = PublicPrivate) implies ()
	**/	
}

pred manualInsertionExample{
	// start
	once CurrentState.state = StartTripCreation
	
	one u: RegisteredUser| updateOnlyUser[u]
	// user inserts new trip into registered trips
	after(CurrentState.state = FirstSegmentCreation)
	
	// now continues to insert segments in path
	after after(CurrentState.state = SegmentInsertion)

/**		after after after(CurrentState.state = SegmentInsertion)
		after after after after(CurrentState.state = SegmentInsertion)
	
		// after insertion computes path score
		after after after after after(CurrentState.state = ComputeScore)
	
		// then user inserts duration
		after after after after after after(CurrentState.state = InsertDuration)
	
		// then system inserts every statistic
		after after after after after after after(CurrentState.state = ComputeStatistics)
		
		// lastly, user chooses to make public or private
		after after after after after after after after(CurrentState.state = PublicPrivate)
	// end
	eventually CurrentState.state = PublicPrivate
**/
}
/**** UTILITY FUNCTIONS and PREDICATES ****/

// show the segments of a path:
fun showPath[p: Path] : set Segment{
	p.start.*nextSegment
}

/**** GENERAL FACTS THAT ALWAYS HOLD ****/
	
fact segmentsFacts{

	// Segments are saved only if associated with another 
	// segment or a Path (and at least an object Path 
	// is needed in the chain)
	all s: Segment| (
		some ss: Segment| 
			ss.nextSegment = s  or 
			some p: Path| p.start = s)

	all s: Segment|
		// if segment is last in chain or in a cycle
		(s.nextSegment = none or s in s.^nextSegment) implies 
		// then from said segment i can walk backwards 
		// until i find a path's start
		(some p: Path | p.start in s.^~nextSegment)
}

fact pathsFacts{
	// Paths are equal if the segments inside 
	// are the same sequence of objects
	all p1,p2: Path|
		p1 != p2 implies (
			showPath[p1] != showPath[p2])
}


run manualInsertionExample for 3 steps 

/**for 50 but 
		exactly 2 RegisteredUser,
		exactly 10 Trip,
		exactly 5 Path,
		exactly 30 Segment
**/
