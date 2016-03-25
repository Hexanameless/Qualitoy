open util/ordering[Time] as to
sig Time {}

sig Position {x, y : Int} //Describe a position, in X or Y

sig Drone {position : Position,
				time : Time } // A drone have a position on the grid 

one sig Entrepot {position : Position} // There is only one warehouse which have a position on the grid

sig Receptacle {position : Position} //There are receptacle which have a position on the grid


pred SoloDrone { //Two drones can not have the same position
	no d0, d1 : Drone | (d0 != d1) &&
									(d0.position = d1.position)
}

pred SoloReceptacle{ //Two Receptacle can not have the same position
	no r0, r1 : Receptacle | (r0 != r1)&& 
											(r0.position = r1.position)
}

pred SoloEntrepot {
	no r : Receptacle, e : Entrepot | r.position = e.position
}

pred SoloPosition{
	no p0, p1 : Position | (p0 != p1) &&
									((p0.x = p1.x) && (p0.y = p1.y))
}

assert DifferentePosition {
	no p0, p1 : Position | (p0 != p1) && (p0.x = p1.x) && (p0.y = p1.y) && SoloReceptacle && SoloEntrepot && SoloDrone && SoloPosition 
}

check DifferentePosition

pred go{}

run SoloDrone for 2 but exactly 2 Drone, 2 Receptacle
run SoloEntrepot for 2 but exactly 2 Receptacle
