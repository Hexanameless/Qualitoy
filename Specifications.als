open util/ordering[Time] as to
sig Time {
	 value : one Int
}

<<<<<<< HEAD
sig Position {x, y : Int,
	d : lone Drone,
	r : lone Receptacle,
	t : one Time,
	e : lone Entrepot
} //Describe a position, in X or Y
=======
sig Position {x, y : Int
					} //Describe a position, in X or Y
>>>>>>> origin/master

sig Drone {
				capacity : Int,
				energie : Int
				 } // A drone have a position on the grid 

<<<<<<< HEAD
one sig Entrepot {} // There is only one warehouse which have a position on the grid

sig Receptacle {
	capacity : Int
} //There are receptacle which have a position on the grid


=======

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
>>>>>>> origin/master

pred AllReceptacleSomewhere{
	all re:Receptacle | one p:Position | p.r=re
}
pred OneEntrepot{
	one p:Position |p.e = Entrepot
}

pred NoReceptacleAtEntrepot{
	no p:Position|(one re:Receptacle|p.r=re)&&p.e = Entrepot
}

//Problem whit making differents successive times
pred defTime{
	all t:Time|((t.value=0||(one t2:Time|Succ[t.value,t2.value]))&&(no t2:Time|(t!=t2&&t2.value=t.value)))
}

pred Succ[v1:Int,v2:Int]{
	v1=v2+1
}

pred capPos{
	all r:Receptacle|r.capacity>0&&all d:Drone|d.capacity>0
}

<<<<<<< HEAD
pred go {
	AllReceptacleSomewhere&&OneEntrepot&&NoReceptacleAtEntrepot&&defTime&&capPos
}

run defTime for 4


=======
pred go{
	DifferentePosition && MaxEnergie && ReceptacleVoisins
}

run go for 2 but exactly 3 Drone, 2 Receptacle, 8 Position
>>>>>>> origin/master
