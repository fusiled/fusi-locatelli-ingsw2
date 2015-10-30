//misc
sig RideStatus{}
sig Taxi{}

sig Zone{
contains: set Taxi
}

sig Ride{
performedBy: one Taxi,
status: one RideStatus,
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

fact allZonesManagedBySystem{
	all z :Zone | z in System.manages  
}

fact allTaxisBelongsToAZone{
	all t :Taxi | t in Zone.contains  and all z1, z2:Zone | (t in z1.contains and t in z2.contains) implies (z1=z2)
}

fact allAbstractPrestationsHaveCustomer{
	all c: Customer | some p:AbstractPrestation | c in p.invokes 
}

fact AllAbstractPrestationsAreLinkedToSystem{
	all p: AbstractPrestation | p in System.handles
}

fact RidesStatusAndRideAssociationIsUnique{
	all r:RideStatus | r in Ride.status and all ride1,ride2:Ride |(r in ride1.status and r in ride2.status) implies (ride1=ride2)
}

fact customerMinimumNumber{
#Customer = 3
}

pred show(){ }
run show
