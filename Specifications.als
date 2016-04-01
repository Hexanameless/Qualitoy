open util/ordering[Time] as to
sig Time {}

sig Position {
	x, y : Int
} //Describe a position, in X or Y

sig Batterie {
	unite : Int one ->Time
}

sig Drone {
	position : Position,
    currentPosition : Position one -> Time,
	commande : Commande lone -> Time,
	capacite : Int,
	batterie : Batterie one
} // A drone have a position on the grid 

sig Receptacle {
	position : Position,
	capacite : Int
} //There are receptacle which have a position on the grid 

one sig Entrepot {
	position : Position
// receptaclesVoisins : some Receptacle        //An Entrepot contains at least one " receptables voisins " (contrainte 13)
} // There is only one warehouse which have a position on the grid

sig Commande {
	produits : Int,
	cible : Receptacle
}

fact soloDrone {  // Two drones can not be on the same position at the same time
    all t : Time | 
	no d0, d1 : Drone |
	d0 != d1 && 
	d0.currentPosition.t = d1.currentPosition.t
}

fact soloDroneParCommande {	// Two drones can not have the same command
	all t : Time |
	no d0, d1 : Drone |
	d0 != d1 &&
	d0.commande.t = d1.commande.t
}

fact soloReceptacle {
	no r0, r1 : Receptacle |
	r0 != r1 &&
	r0.position = r1.position
}

fact  CapBatterie {
	all b : Batterie | all t : Time | b.unite.t <= 3
}//La capacité de la batterie d’un drone est de 3 unités d’énergie.


fact ConsommeEnergie {
	 all d : Drone | all t,t1 : Time | t1!=t.next && d.currentPosition.t = d.currentPosition.t1 || d.batterie.t1.unite = minus[d.batterie.t.unite,1]
}//Un drone consomme 1 unité d’énergie pour faire 1 pas sur la grille.

fact grilleReduite {
	all p : Position | p.x>=0 && p.x<=6 && p.y>=0 && p.y<=6
}


fact soloDeplacement {
	all d : Drone | all t,t1 : Time | t1!=t.next || distanceManhattan[d.currentPosition.t, d.currentPosition.t1] < 2 
}

fact soloCapaDrone {
	all d1, d2 : Drone | d1.capacite = d2.capacite && d1.capacite > 0
}

fact soloCapaRecep {
	all r1, r2 : Receptacle | r1.capacite = r2.capacite && r1.capacite > 0
}

fact tailleCommandeDrone {
	all c : Commande | no d : Drone | c.produits > d.capacite
}

fact tailleCommandeRecep {
	all c : Commande | no r : Receptacle | c.produits > r.capacite
}

fact dnb {
	#Drone = 3
}

fact rnb {
	#Receptacle = 5
}

fact entrepotDiffReceptacle {
	no e : Entrepot | some r1 : Receptacle | e.position = r1.position
} // un receptacle et un entrepot ne peuvent pas etre sur la meme position


fact soloPosition  {
	no p0, p1 : Position |
	p0 != p1 &&
	(p0.x = p1.x &&
	p0.y = p1.y)
}

fun absoluteValue [ a : Int ] : Int {
    a>=0 => a 
    else mul[-1,a] 
}

fun distanceManhattan [ p1, p2 : Position ] : Int {
    plus [ absoluteValue [ minus[p1.x, p2.x] ] ,  absoluteValue [ minus[p1.y, p2.y] ] ]
}


/*
assert A1 {
	no p0, p1 : Position |
	p0 != p1 &&
	p0.x = p1.x &&
	p0.y = p1.y
}

check A1 for 3 but exactly 3 Receptacle
---------------------------------------------*/

pred voisin [ p : Position ]{ // voisin : distance de manhattan = 1 unité
   some  r : Receptacle | (p.y= r.position.y && ((minus [p.x , r.position.x]=1 ) or ( minus [p.x , r.position.x]=-1 )))
    or ( p.x= r.position.x && (( minus [p.y , r.position.y]=1 ) or (minus [p.y , r.position.y]=1))) 
}

pred voisinEntrepot {
    one e : Entrepot |
	voisin [ e.position ]
}


pred distanceReceptacle { // contrainte 14
	no r1: Receptacle | all r2:Receptacle | ( ( r1!=r2 ) && ( distanceManhattan [r1.position,r2.position] > 3 ))
}

pred testM {
	some p0, p1 : Position |
	p0.x = 2 &&
	p0.y =2 &&
	p1.x = 1 &&
	p1.y = 1 &&
	distanceManhattan[p0, p1] = 2
}



//run testM for 2 but exactly 2 Position

pred go {
  distanceReceptacle &&  voisinEntrepot
}

/*assert test {
	some r1 : Receptacle | all r2 : Receptacle | r1!=r2 && distanceManhattan[r1.position, r2.position] > 3 
}

 check test for 4 but exactly 4 Receptacle, 6 Int */

run go for 2 but exactly 3 Receptacle,4 Position
/*fun EstAccessible [ p : Position ] : Int {
    one e : Entrepot | ( DistanceManhattan [e.position,  p ] = 1 
}*/
run testM for 2 but exactly 2 Position
