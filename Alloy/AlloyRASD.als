/*******************  CLASSES  *******************/

sig Position {}

sig User {
			position: one Position
}

sig SafeArea {
			position: one Position
}

sig PowerGridStation extends SafeArea {}

sig Car {
			parked: one SafeArea {}
}

sig ReservedCar extends Car {}

sig Reservation {
			driver: one User
			reservedCar: one ReservedCar
}

sig Transaction {
			owner: one User
			details: one Reservation
}

/*******************  CONSTARAINTS  *******************/

// ensure that all car marked as reserved are associated to only one reservation

fact AllReservedCarAreAssociatedToAReservation{
			all c:ReservedCar | one r:Reservation | r.reservedCar = c
}

// ensure that for a pair [user, reservation], only one transaction exists

fact OnlyOneTransctionForEachUserAndReservation{

}




/*******************  ASSERTIONS  *******************/


/*******************  PREDICATES  *******************/



