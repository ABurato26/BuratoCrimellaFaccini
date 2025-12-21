/**** Best Bike Paths model for alloy specification ****/

/** For readability and simplicity motivations we decided to not completely
	use every possible object of the model (Nodes are modeled without 
	coordinates data and so equality is by object, not value).**/

/** For modelling purposes, segments are different even if physically not 
	(imagine a map-like interaction with common nodes, where two nodes are
	identical iff they're the same and are traversed in the same 
	direction) **/

/*** SIGNATURES ***/
abstract sig Status{}
one sig Clear extends Status{}
one sig RoadWork extends Status{}
one sig Pothole extends Status{}

sig Segment{
	nextSegment: lone Segment,
	status: some Status
}

sig Path{
	start: one Segment,
	score: Int
}

sig Statistics{}

sig Trip{
	path: one Path,
	allStats: one Statistics
}

sig RegisteredUser {
	registeredTrips: set Trip,
	publishedTrips: set Trip
}

// a path is always linked to a trip
fact pathsLinkedToTrips{
	all p: Path|(
		some t: Trip|(
			p in t.path
		)
	)
}

// statistics are always linked to a trip
fact statisticsLinkedToTrips{
	all s: Statistics|(
		some t: Trip|(
			s in t.allStats
		)
		
		// for better displaying, all statistics are different
		and all t1,t2: Trip|(
			t1!=t2 and
			s = t1.allStats implies s != t2.allStats
		)
	)
}

// trips linked to users
fact tripsLinkedToUsers{
	all t: Trip|(
		some u: RegisteredUser|(
			t in u.registeredTrips
		)
	)
}

// a user has at least one registered trip
fact userHasTrips{
	all u: RegisteredUser|(
		#(u.registeredTrips) > 0
	)
}

// published trips are subset to all registered trips
fact publishedTripsIsSubset{
	all u: RegisteredUser|(
		publishedTrips[u] in registeredTrips[u]
	)
}

// no segments exist before head segment 
fact startsAreHeads {
    all p: Path |(
      	no s: Segment |(
			s in p.start.^nextSegment
			and s.nextSegment = p.start
		)
	)
}

// no trips are in common between users
fact uniqueTrips{
	all u1,u2: RegisteredUser|(
		all t: Trip|(
			u1 != u2 and
			(t in u1.registeredTrips) implies
			(t not in u2.registeredTrips)
		)
	)
}

// rules for coherent paths
fact coherentPaths{
	// Segments are saved only if associated with another 
	// segment or a Path (and at least an object Path 
	// is needed in the chain)
	all s: Segment| (
		some ss: Segment|( 
			ss.nextSegment = s or 
			some p: Path|(
				s = p.start
			)
		)
	)

	all s: Segment|(
		// if segment is last in chain or in a cycle
		(s.nextSegment = none or s in s.^nextSegment) implies 
		// then from said segment i can walk backwards 
		// until i find a path's start
		some p: Path|(
			p.start in s.^~nextSegment
		)
	)
	
	// avoid self loops
	all s1, s2: Segment|(
		(s2 in s1.^nextSegment) implies (s1 not in s2.^nextSegment)
		
	)
}

// show the segments of a path:
fun showPath[p: Path] : set Segment{
	p.start.*nextSegment
}

// collapse identical paths
fact pathEquality{
	// Paths are equal if the segments inside 
	// are the same sequence of objects
	all p1,p2: Path|
		p1 != p2 implies (
			showPath[p1] != showPath[p2])
}

run example{} for 20 but 
	exactly 3 RegisteredUser,
	exactly 4 Trip,
	exactly 3 Path,
	exactly 6 Segment

run example{} for 20 but
	exactly 5 RegisteredUser,
	exactly 6 Trip,
	exactly 1 Path,
	exactly 3 Segment
