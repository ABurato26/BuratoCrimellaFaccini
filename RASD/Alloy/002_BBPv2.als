/**** Best Bike Paths model for alloy specification ****/

/** For readability and simplicity motivations we decided to not completely
	use every possible object of the model (Nodes are modeled without 
	coordinates data and so equality is by object, not value). Variable
	objects are surely  **/

abstract sig Status{}				// status of the roads (expandible)
one sig Clear extends Status{}
one sig Hole extends Status{}

sig Statistics{}{
	// Statistics are saved only if associated with at least a trip
	some t: Trip| t.averageSpeed = this 
	or t.duration = this 
	or t.externalStats = this
}					

sig Node{}{
	some s: Street| s.nodeA = this or s.nodeB = this
}

sig Street{
	status: one Status,
	nodeA: Node,
	nodeB: Node
}{
	// no streets that are points
	nodeA != nodeB
	
	//Streets are saved only if associated with at least a path
	and some p: Path| this in p.sequence.elems
}

sig Path{
	sequence: seq Street,
	score: Int
}{
	// A Path has always at least one Street
	#sequence>0

	// Paths are saved only if associated with at least a Trip
	//and some t: Trip| t.path = this
}

sig Trip{
	path: one Path,
	averageSpeed: one Statistics,
	duration: one Statistics,
	externalStats: lone Statistics
}{
	// statistics are different
	averageSpeed != duration and duration != externalStats

	// Trips are saved only if associated with at least a registered user
	some u: RegisteredUser| this in u.registeredTrips
}

sig RegisteredUser {
	registeredTrips: set Trip,
	publishedTrips: set Trip
}{
	publishedTrips in registeredTrips
}

/**** UTILITY FUNCTIONS and PREDICATES ****/

/** Allows to understand if two streets are well connected **/
pred wellConnected(s1: Street, s2: Street){
	s1.nodeB = s2.nodeA
} 

/**** GENERAL FACTS THAT ALWAYS HOLD ****/

/** When building a path, it is mandatory that streets are well connected
	(such as NodeB of the i street is connected to NodeA of the i+1 street) 
**/
fact wellConnectedStreets{
	all p: Path|
		all i: p.sequence.inds - max[p.sequence.inds]|
			wellConnected[p.sequence[i],p.sequence[i+1]]
}

run {} for 20 but 
		exactly 1 Trip,
		exactly 1 Path,
		exactly 3 Street
