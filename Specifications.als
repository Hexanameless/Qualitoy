sig Coordonnee{} //Describe a position, in X or Y
abstract sig Position {
	abscisse, ordonnee : Coordonnee
}

sig Drone {position : Position } // A drone have a position on the grid 

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


pred go{}

run SoloReceptacle
