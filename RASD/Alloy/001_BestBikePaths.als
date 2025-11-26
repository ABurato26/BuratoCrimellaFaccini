// Best Bike Paths model for alloy specification

sig Coordinates{}

sig Statistics{}

sig Node{
	position: one Coordinates
}

sig Path{
	start: one Node,
	middle: set Node,
	end: one Node
}

sig Trip{
	path: one Path,
	internalStats: one Statistics,
	externalStats: lone Statistics
}

sig User{
	
}

sig RegisteredUser extends User{
	registeredTrips: set Trip
}

// every trip has a user that registered itUser
fact tripsFromUsers{
	all t: Trip| one ru: RegisteredUser | t in ru.registeredTrips
}

// every trip is different (even if the path could be the same)
fact differentTrips{
    all ru1, ru2: RegisteredUser |
        ru1 != ru2 implies no (ru1.registeredTrips & ru2.registeredTrips)
}

// coordinates of start, middle and finish must be different
fact differentCoordinates{
	all p: Path| (p.start != p.end)  
}

// brute force number of trips
fact threeTripsForUser{
	all ru: RegisteredUser| #(ru.registeredTrips) = 3
}


run {} for
    30
    but exactly 4 RegisteredUser,
        exactly 12 Trip,
        exactly 9 Path,
        exactly 15 Node,
        exactly 15 Coordinates,
        exactly 9 Statistics
