/**** Best Bike Paths model for alloy specification ****/
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
	score: lone Int,
	start: one Segment
	
}

sig Statistics{}

sig Trip{
	tripStatistics: one Statistics,
	var path: one Path
}

sig RegisteredUser {
	registeredTrips: set Trip,
	publishedTrips: set Trip
}

/*** FACTS ***/

// a path is originally linked to a trip
fact pathsLinkedToTrips{
	once(
		all p: Path|(
			some t: Trip|(
				p in t.path
			)
		)
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
			s.nextSegment = p.start
		)
	)
}

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

pred merge[u1: RegisteredUser, u2: RegisteredUser - u1]{
    one p1, p2: Path |(
       	p1 in u1.registeredTrips.path and
       	p2 in u2.registeredTrips.path and
       	#(p1.start.^nextSegment) = #(p2.start.^nextSegment)

		// from now, p2 is the fresher path so p1 needs to be disconnected
 		// trips formerly on p1 now point to p2
       	and all t: Trip | (
    		((t.path = p1) implies (t.path' = p2))
    		and
    		((t.path != p1) implies (t.path' = t.path))
		)

   		// statistics unchanged (new score is the same as p2)
	)
}

// fact equalPaths{}			here deleted (because of merging)

pred mergingPathExample {
	// at the start, at least a trip points to all paths
	all p: Path|(
		some t: Trip|(
			p in t.path
		)
	)
	// same for user - trips
	all t: Trip|(
		some u: RegisteredUser|(
			t in u.registeredTrips
		)
	)
	// give a feasible scenario
    one u1, u2: RegisteredUser|(     // pick two users
    	some t1, t2: Trip|(
       		t1 in u1.registeredTrips and
       		t2 in u2.registeredTrips and
       		merge[u1,u2]
    	)
	)
}

run mergingPathExample for 
	exactly 2 RegisteredUser, 
	exactly 2 Trip, 
	exactly 2 Path, 
	exactly 8 Segment, 
	3 Statistics, 
	5 Int
