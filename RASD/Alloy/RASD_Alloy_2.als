/*******************  CLASSES  *******************/

// power grid station status
abstract sig StationStatus {}
// the power grid station is free
one sig Free extends StationStatus {}
// there is a car plugged into the power grid station
one sig InUse extends StationStatus {}

// battery level of the car
abstract sig BatteryLevel {}
// the level of the battery is high (>50%)
one sig High extends BatteryLevel {}
// the level of the battery is medium
one sig Medium extends BatteryLevel {}
// the level of the battery is low (<20%)
one sig Low extends BatteryLevel {}

// indicate if the car is plugged into a power grid station
abstract sig ChargingStatus {}
// the car is plugged into a power grid station
one sig Charging extends ChargingStatus {}
// the car is not plugged into a power grid station
one sig NotCharging extends ChargingStatus {}

// status of the car
abstract sig CarStatus {}
// the car is parked and somone reserved it
one sig Reserved extends CarStatus {}
// the car is parked and none reserved it
one sig NotReserved extends CarStatus {}
// the user picked up the car
one sig BeingDrived extends CarStatus {}

// distance of the car from the nearest power grid station
abstract sig Distance {}
// the car is far (distance >3Km)
one sig Far extends Distance {}
// the car is near (distance <= 3Km)
one sig Near extends Distance {}

// status of the reservation
abstract sig ReservationStatus {}
// the user has one hour to go and pick up the car
one sig Valid extends ReservationStatus {}
// the user picked up the car
one sig UserDriving extends ReservationStatus {}
// the user parked the car after the ride
one sig EndOfTheRide extends ReservationStatus {}
// the user let the resevation expire
one sig Expired extends ReservationStatus {}

sig Position {}

sig User {}

// parking area for a certain number of car 
// (in this model, for simplicity, we consider only one car)
sig SafeArea {
	position: one Position
}

// the parking area can have  a certain number of power grid station where a car can be plugged in 
// (in this model, for simplicity, we consider only one power grid statio)
sig PowerGridStation extends SafeArea {
	status: one StationStatus
}

abstract sig Car {
	status: one CarStatus,
	position: one Position,
	batteryLevel: one BatteryLevel,
} 

// a car that someone is driving
sig UnlockedCar extends Car {} 

// a car that can be reserved or not, it can be connected to a power grid station (charging) or it can be at some distance 
// from a power grid station (distance)
sig LockedCar extends Car { 
	chargingStatus: one ChargingStatus,
	distance: one Distance
}

sig Passenger {}

sig Reservation {
	user: one User,
	reservedCar: one Car,
	reservationStatus: one ReservationStatus,
	passengers: some Passenger
}

sig Transaction {
	owner: one User,
	reservation: one Reservation,
	fee: Int
}

/*******************  CONSTARAINTS  *******************/

// 1 - ensure that all locked car are in a safe area
fact AllLockedCarInASafeArea{
	all c: LockedCar | one s: SafeArea | c.position = s.position
}

// 2 - ensure that all locked car marked as charging are in a safe area with a power grid station 
fact AllChargingCarInASafeAreaWithPowerGridStation{
	all c: LockedCar | one p: PowerGridStation | c.chargingStatus = Charging implies c.position = p.position 
}

// 3 - ensure that all unlocked car are not in a safe area
fact AllUnlockedCarNotInASafeArea{
	all c: UnlockedCar | all s: SafeArea | c.position != s.position
}

// 4 - ensure that a locked car is not in the same safe area of another car
fact OnlyOneLockedCarPerSafeArea{
	all disj c1, c2: LockedCar | c1.position != c2.position
}

// 5 - ensure that in all power grid station marked as not free there is a car charging
fact AllPowerGridStatioNotFree{
	all p: PowerGridStation | one c: LockedCar | c.position = p.position && (c.chargingStatus = Charging iff p.status = InUse)
}

// 6 - ensure that a locked car in the same position of a power grid station is flagged as "Near"
fact AllLockedCarInASafeAreaWithPowerGridStationFlaggedAsNear{
	all c: LockedCar | one p: PowerGridStation | c.position = p.position implies c.distance = Near
}

// 7 - ensure that there is only one safe area in one position
fact OnlyOneSafeAreaInOnePosition{
	all disj s1, s2: SafeArea | s1.position != s2.position
}

// 8 - ensure that there is only one unlocked car in one position
fact OnlyOneSafeAreaInOnePosition{
	all disj u1, u2: UnlockedCar | u1.position != u2.position
}

// 9 - ensure that all unlocked cars are associated to a reservation
fact AllUnlockedCarAreReserved{
	all u: UnlockedCar | one r: Reservation | r.reservedCar = u
}	

// 10 - ensure that all locked cars flagged as "Reserved" are associated to a reservation
fact AllReservedLockedCarAreAssociatedToAReservation{
	all c: LockedCar | one r: Reservation | c.status = Reserved implies r.reservedCar = c
}

// 11 - ensure that all distinct reservation refers to different cars
fact AllReservationAreForDifferentCars{
	all disj r1, r2: Reservation | r1.reservedCar != r2.reservedCar 
}

// 12 - ensure that all distinct reservation refers to different users
fact AllReservationAreForDifferentUsers{
	all disj r1, r2: Reservation | r1.user != r2.user 
}

// 13 - ensure that all distinct reservation refers to different passengers
fact AllReservationAreForDifferentPassengers{
	all disj r1, r2: Reservation | disj[r1.passengers , r2.passengers]
}

// 14 - ensure that all valid reservation are associated to a reserved locked car
fact AllValidReservationAreAssociatedToALockedCar{
	all r: Reservation | r.reservationStatus = Valid implies r.reservedCar.status = Reserved
}	

// 15 - ensure that all reservation flagged as "Expired" or "EndOfTheRide" are associated to a not reserved locked car
fact AllValidReservationAreAssociatedToALockedCar{
	all r: Reservation | (r.reservationStatus = Expired or r.reservationStatus = EndOfTheRide) implies r.reservedCar.status = NotReserved
}	

// 16 - ensure all unlocked car are flagged as "BeingDrived"
fact AllUnlockedCarAreFlaggedAsBeingDrived{
	all u: UnlockedCar | u.status = BeingDrived
}

// 16a - ensure all locked car are not flagged as "BeingDrived"
fact AllLockedCarAreNotFlaggedAsBeingDrived{
	all c: LockedCar | c.status != BeingDrived
}

// 17 - ensure that all reservation flagged as "UserDriving" are associated to an unlocked car
fact AllValidReservationAreAssociatedToALockedCar{
	all r: Reservation | r.reservationStatus = UserDriving iff r.reservedCar.status = BeingDrived
}

// 18 - ensure that all transactions have the same owner of the corresponding reservation 
fact AllTransactionAndCorrespondingReservationWithSameUser{
	all t: Transaction | t.owner = t.reservation.user
}

// 19 - ensure that all transactions have a non negative fee
fact AllTransactionsHaveANotNegativeFee{
	all t: Transaction | t.fee >= 0
}

// 20 - ensure that all transactions refers to different reservation 
fact AllTransactionRefersToDifferentReservations{
	all disj t1, t2: Transaction | t1.reservation != t2.reservation
}

// 21 - ensure that all reservation are related to a transaction
fact AllReservationRelatedToATransaction{
	all r: Reservation | one t: Transaction | t.reservation = r
}

// 22 - ensure that all transaction that refers to "Valid" reservation have fee equal to zero
// -> the ride is not started yet: the fee will be once the user starts driving
fact AllTransactionThatRefersToAValidOrUserDrivingReservationHaveFeeZero{
	all t: Transaction | (t.reservation.reservationStatus = Valid) implies t.fee = 0
}

// 23 - ensure that all transaction that refers to an "Expired" reservation have fee equal to one
fact AllTransactionThatRefersToAExpiredReservationHaveFeeOne{
	all t: Transaction | (t.reservation.reservationStatus = Expired) implies t.fee = 1
}

// 24 - ensure that all transaction that refers to a "UserDriving" or "EndOfTheRide" reservation have fee greater than one
fact AllTransactionThatRefersToAEndOfTheRideReservationHaveFeeGreaterThanOne{
	all t: Transaction | (t.reservation.reservationStatus = UserDriving or t.reservation.reservationStatus = EndOfTheRide) implies t.fee > 1
}

/*******************  ASSERTIONS  *******************/

// 1 - check that all locked car marked as charging are in a safe area with a power grid station 
assert AllChargingCarInASafeAreaWithPowerGridStation{
			no c: LockedCar | all p: PowerGridStation | c.chargingStatus = Charging && c.position != p.position 
}
check AllChargingCarInASafeAreaWithPowerGridStation

// 2 - check that a locked car is not in the same safe area of another car
assert OnlyOneLockedCarPerSafeArea{	
			no disj c1, c2 : LockedCar | c1.position = c2.position
}
check OnlyOneLockedCarPerSafeArea

// 3 - check that there is only one safe area in one position
assert OnlyOneSafeAreaInOnePosition{
			no disj s1, s2: SafeArea | s1.position = s2.position
}
check OnlyOneSafeAreaInOnePosition

// 4 - check that there is only one unlocked car in one position
assert OnlyOneUnlockedCarInOnePosition{
			no disj u1, u2: UnlockedCar | u1.position = u2.position
}
check OnlyOneUnlockedCarInOnePosition

// 5 - check that all distinct reservation refers to different cars
assert AllReservationAreForDifferentCars{
			no disj r1, r2: Reservation | r1.reservedCar = r2.reservedCar 
}
check AllReservationAreForDifferentCars

// 6 - check that all distinct reservation refers to different users
assert AllReservationAreForDifferentUsers{
			no disj r1, r2: Reservation | r1.user = r2.user 
}
check AllReservationAreForDifferentUsers

// 7 - check that all transactions have the same owner of the corresponding reservation 
assert AllTransactionAndCorrespondingReservationWithSameUser{
			no t: Transaction | t.owner != t.reservation.user
}
check AllTransactionAndCorrespondingReservationWithSameUser


// 8 - check that all transactions have a positive fee
assert AllTransactionsHaveAPositiveFee{
			no t: Transaction | t.fee < 0
}
check AllTransactionsHaveAPositiveFee

// 9 - check that all transactions refers to different reservation 
assert AllTransactionRefersToDifferentReservations{
			all disj t1, t2: Transaction | t1.reservation != t2.reservation
}
check AllTransactionRefersToDifferentReservations

/*******************  PREDICATES  *******************/

pred showAll() {
			#UnlockedCar > 1
}
run showAll for 5 but exactly 3 LockedCar

pred showLockedCar() {}
run showLockedCar for 5 but exactly 3 LockedCar

pred showUnlockedCar() {}
run showUnlockedCar for 3 but exactly 3 UnlockedCar
