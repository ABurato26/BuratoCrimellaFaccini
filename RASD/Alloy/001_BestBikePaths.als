// Best Bike Paths model for alloy specification

abstract sig Status{}
one sig Clear extends Status{}
one sig Hole extends Status{}

sig Score{}

sig Statistics{}

sig Street{
	status: one Status
}

sig Path{
	sequence: seq Street,
	score: Score
}{
	#sequence>0
}

sig Trip{
	path: one Path,
	averageSpeed: one Statistics,
	duration: one Statistics,
	externalStats: lone Statistics
}{
	averageSpeed != duration and duration != externalStats
}

sig RegisteredUser {
	registeredTrips: set Trip
}

// one street cannot have itself as following
fact noSameFollowingStreet{
	all p: Path|
		all i: p.sequence.inds - max[p.sequence.inds]|
			p.sequence[i] != p.sequence[i+1]
}

// a street exists only if connected with a path
fact streetsExistsWithPaths{
	all s: Street|
		some p: Path|
			s in p.sequence.elems
}

// a path exists only if connected with a trip
fact pathsExistWithTrips{
	all p: Path|
		some t: Trip|
			t.path = p
		
}

// a statistic exists only if connected with a trip
fact statisticsExistWithTrips{
	all s: Statistics|
		some t: Trip|
			t.averageSpeed = s or
			t.duration = s or
			t.externalStats = s
}

// a trip exists only if connected with a user that registered it
fact tripsExistWithUsers{
	all t: Trip|
		some u: RegisteredUser|
			t in u.registeredTrips
}

// every trip is different (even if the path could be the same)
fact differentTripsForDifferentUsers{
	all t1, t2: Trip|
		all u1, u2: RegisteredUser|
			((t1 in u1.registeredTrips) and (t2 in u2.registeredTrips) and (t1 = t2))
			implies
			(u1 = u2)
}


run {} for
    40
    but exactly 8 RegisteredUser,
        exactly 6 Street,
        exactly 10 Trip
