//Time is in milliseconds after the unix date
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
memorize: set Ride,
handles: set AbstractPrestation,
manages: set Zone
}

//prestations
abstract sig AbstractPrestation{
invokes: one Customer
}


sig Request extends AbstractPrestation{}

sig Reservation extends AbstractPrestation{
arrivalTime: Int
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

fact allRidesMemorizedBySystem{
	all r :Ride | r in System.memorize  
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

fact maximumToleranceOfArrivalTime{
	all rid: Ride | some res: Reservation | (res in rid.executes) implies ((res.arrivalTime <= rid.executedAt + 300000) or (res.arrivalTime >= rid.executedAt - 300000))
}

fact reservationMustBeMadeAtLeastTwoHoursBeforeTheRide{
	all res:Reservation | some rid:Ride | (res in rid.executes) implies (res.arrivalTime < rid.executedAt - 7200000)
}

pred addRequest[s, s': System, r:Request]{
	s'.handles = s.handles + r
}

pred addReservation[s, s': System, r:Reservation, time: Int]{
	r.arrivalTime = time and
	s'.handles = s.handles + r
}

pred addRideMadeFromReservation[s, s': System, r:Ride, ex:Int, fin:Int, t:Taxi, stat:Int, res:Reservation]{
	r.executedAt = ex and
	r.finishedAt = fin and
	r.performedBy = t and
	r.executes = res and
	s'.memorize = s.memorize + r	
}

assert checkAddedRequest{
	all s, s': System, r: Request | addRequest[s, s', r] implies (r in s'.handles)
}
check checkAddedRequest

assert checkAddedReservation{
	all s, s': System, r: Reservation | addReservation[s, s', r, 1000] implies (r in s'.handles)
}
check checkAddedReservation

assert checkWrongRide{
	no s,s':System , r:Ride, t:Taxi , res:Reservation | all exTime, resTime:Int | addRideMadeFromReservation[s,s',r,exTime,exTime+10,t,0,res] and addReservation[s,s',res,resTime] and(exTime - resTime < 7200000) 
}
check checkWrongRide

pred show(){ }
run show
run addRequest
run addReservation
run addRideMadeFromReservation
