/**** Best Bike Paths model for alloy specification ****/

/** For readability and simplicity motivations we decided to not completely
	use every possible object of the model (Nodes are modeled without 
	coordinates data and so equality is by object, not value).**/

/** For modelling purposes, segments are different even if not (imagine a
	map-like interaction with common nodes **/

// status of the roads (expandible)
abstract sig Status{}				
one sig Clear extends Status{}
one sig RoadWork extends Status{}
one sig Pothole extends Status{}

sig Segment{
	nextSegment: lone Segment,
	status: some Status
}{
	// a segment cannot point to itself as next 
	// (but cycles are allowed)
	nextSegment != this 

	// if status is clear then its the only status possible
	Clear in status implies #status = 1
}

sig Path{
	start: Segment,
	score: Int
}{
	// Paths are saved only if associated with 
	// at least a Trip
	some t: Trip| t.path = this
}

sig Statistics{}{
	// Statistics are saved only if associated 
	// with at least a trip
	some t: Trip| t.averageSpeed = this 
	or t.duration = this 
	or t.externalStats = this
}					

sig Trip{
	path: one Path,
	averageSpeed: one Statistics,
	duration: one Statistics,
	externalStats: lone Statistics
}{
	// statistics are different
	averageSpeed != duration and duration != externalStats

	// Trips are saved only if associated with 
	// at least a registered user
	one u: RegisteredUser| this in u.registeredTrips
}

sig RegisteredUser {
	registeredTrips: set Trip,
	publishedTrips: set Trip
}{
	// published trips are a subset of all registered trips
	publishedTrips in registeredTrips 
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


/** When building a path, it is mandatory that streets are well connected
	(such as NodeB of the i street is connected to NodeA of the i+1 
	street) **/

run {} for 50 but 
		exactly 10 Trip,
		exactly 7 Path,
		exactly 30 Segment
