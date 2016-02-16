/********************************************************************

				mytaxy ALLOY MODEL
	AUTHORS: Matteo Maria Fusi, Matteo Locatelli                
                                                                                            
**********************************************************************/


/**
NOTES
- Binary variables such as available and status has been modeled with Int
	 that assumes value 0 or 1
- Time variables such as executedAt, finishedAt and arrivalTime are Int
	that express milliseconds after the unix date
*/

/** SIGNATURES */

//taxis in the city
sig Taxi{
// 0 -> not available, 1 -> available
available: Int //binary
}

//zones of the city
sig Zone{
contains: set Taxi //taxis in a zone
}

//when a prestation takes place a ride is generated
sig Ride{
executedAt: Int, //time
finishedAt: Int, //time
performedBy: one Taxi,
status: Int, // 0-> ride ended, 1 -> ride is taking place
executes: one AbstractPrestation //prestation that a ride executes
}

//who requests prestations
sig Customer{}

//it manages zones, rides and prestations
sig System{
memorize: set Ride,
handles: set AbstractPrestation,
manages: set Zone
}

//prestations
abstract sig AbstractPrestation{
invokes: one Customer //who requests the prestation
}

//request is the base implementation
sig Request extends AbstractPrestation{}

//reservation
sig Reservation extends AbstractPrestation{
arrivalTime: Int //time
}


/** FACTS */

//support facts
fact availableIsBinary{
	all t:Taxi | (t.available = 0) or (t.available = 1)
}

fact rideStatusIsBinary{
	all r:Ride | (r.status = 0) or (r.status = 1)
}


//modelization

//system must be unique
fact oneSystem {
	#System=1
}

fact allZonePointedBySystem{
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

fact allRideMustHaveAPrestation{
	all r : Ride | one p : AbstractPrestation | p in r.executes
}
/** NOTE
As said above, all rides must have an AbstractPrestation instance associated,
	but the inverse is not necessary true. For instance, when an AbstractPrestation
	doesn't take place (all taxi drivers refuse the request) the ride doesn't take
	place*/

fact aTaxiCannotMakeTwoRidesAtTheSameTime{
	some r1:Ride | some r2:Ride | r1.executedAt=r2.executedAt  	implies r1.performedBy != r2.performedBy
}

fact theEndOfARideIsAfterItsBeginning {
	all r:Ride | r.executedAt < r.finishedAt
}

fact aTaxiIsAvailableIfIsNotRunning{
	all t:Taxi | (t.available = 0) implies ( one r:Ride | (t in r.performedBy) and r.status = 1)
}

//tolerance is set to 5 minutes= 300000 milliseconds
fact maximumToleranceOfArrivalTime{
	all rid: Ride | some res: Reservation | (res in rid.executes) implies ((res.arrivalTime <= rid.executedAt + 300000) or (res.arrivalTime >= rid.executedAt - 300000))
}
//2 hours are 7200000 milliseconds
fact reservationMustBeMadeAtLeastTwoHoursBeforeTheRide{
	all res:Reservation | some rid:Ride | (res in rid.executes) implies (res.arrivalTime < rid.executedAt - 7200000)
}

pred addRequest[s, s': System, r:Request]{
	s'.handles = s.handles + r
}



/** PREDICATES AND ASSERTIONS */

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

//try to add an illegal ride.
// this should violate the reservationMustBeMadeAtLeastTwoHoursBeforeTheRide fact.
assert checkWrongRide{
	no s,s':System , r:Ride, t:Taxi , res:Reservation | all exTime, resTime:Int | addRideMadeFromReservation[s,s',r,exTime,exTime+10,t,0,res] and addReservation[s,s',res,resTime] and(exTime - resTime < 7200000) 
}
check checkWrongRide

pred show(){}


/** RUN COMANDS */
run show for 15 but exactly 30 Taxi
run addRequest
run addReservation
run addRideMadeFromReservation
