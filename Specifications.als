open util/ordering[Time] as to
sig Time {}

sig Position {x, y : Int
					} //Describe a position, in X or Y

sig Drone {position : Position,
				time : Time,
				capacity : Int,
				energie : Int
				 } // A drone have a position on the grid 


sig Receptacle {position : Position} //There are receptacle which have a position on the grid 


one sig Entrepot {position : Position,
							 receptaclesVoisins : some Receptacle    	//An Entrepot contains at least one " receptables voisins " (contrainte 13)
							} // There is only one warehouse which have a position on the grid

pred ReceptacleVoisins {
	all e : Entrepot | (e.position.y= e.receptaclesVoisins.position.y && (minus [e.position.x , e.receptaclesVoisins.position.x]=1 ) or ( minus [e.position.x , e.receptaclesVoisins.position.x]=-1 ))
	or ( e.position.x= e.receptaclesVoisins.position.x && ( minus [e.position.y , e.receptaclesVoisins.position.y]=1 ) or (minus [e.position.y , e.receptaclesVoisins.position.y]=1)) 
}

pred SoloDrone { //Two drones can not have the same position at the same time
	no d0, d1 : Drone | (d0 != d1) &&
									(d0.position = d1.position) && (d0.time = d1.time)
}

pred SoloReceptacle{ //Two Receptacle can not have the same position
	no r0, r1 : Receptacle | (r0 != r1)&& 
											(r0.position = r1.position)
}

pred SoloEntrepot {//There is only one Entrepot
	no r : Receptacle, e : Entrepot | r.position = e.position
}

pred SoloPosition{//Two Position have different coordinates
	no p0, p1 : Position | (p0 != p1) &&
									((p0.x = p1.x) && (p0.y = p1.y))
}

pred DifferentePosition {
 SoloReceptacle && SoloEntrepot && SoloDrone && SoloPosition 
}
pred MaxEnergie {
	all d : Drone | d.energie <= 3 && d.energie >= 0
}



pred go{
	DifferentePosition && MaxEnergie && ReceptacleVoisins
}

run go for 2 but exactly 3 Drone, 2 Receptacle, 8 Position
