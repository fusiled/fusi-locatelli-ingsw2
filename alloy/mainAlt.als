//misc
sig Taxi{
available: Int
}

sig Zone{
contains: set Taxi
}

sig Ride{
executedAt: Int,
finishedAt: Int,
performedBy: one Taxi,
status: Int,
executes: one AbstractPrestation
}

sig Customer{
}

sig System{
handles: set AbstractPrestation,
manages: set Zone
}

//prestations
abstract sig AbstractPrestation{
invokes: one Customer
}


sig Request extends AbstractPrestation{}

sig Reservation extends AbstractPrestation{
}


fact oneSystem {
	#System=1
}

fact availableIsABoolean{
	all t:Taxi | (t.available = 0) or (t.available = 1)
}

fact rideStatusIsABoolean{
	all r:Ride | (r.status = 0) or (r.status = 1)
}

fact allZonesManagedBySystem{
	all z :Zone | z in System.manages  
}

fact allTaxisBelongsToAZone{
	all t :Taxi | t in Zone.contains  and all z1, z2:Zone | (t in z1.contains and t in z2.contains) implies (z1=z2)
}

fact allAbstractPrestationsHaveCustomer{
	all p:AbstractPrestation | one c: Customer  | c in p.invokes 
}

fact AllAbstractPrestationsAreLinkedToSystem{
	all p: AbstractPrestation | p in System.handles
}

fact allPrestationsBelongsToARide{
	all p : AbstractPrestation | one r : Ride | p in r.executes
}

fact aRideCannotStartAndEndAtTheSameTime{
	all r:Ride | r.executedAt != r.finishedAt
}

fact aTaxiCannotMakeTwoRidesAtTheSameTime{
	some r1:Ride | some r2:Ride | r1.executedAt=r2.executedAt  	implies r1.performedBy != r2.performedBy
}

fact theEndOfARideIsAfterItsBeginning {
	all r:Ride | r.executedAt < r.finishedAt
}

fact aTaxiIsAvailableIfIsNotRunning{
	all t:Taxi | (t.available = 0) implies ( one r:Ride | (t in r.performedBy) and r.status = 1)
}

pred show(){ }
run show
