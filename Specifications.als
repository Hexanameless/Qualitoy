open util/ordering[Time] as to
sig Time {}

sig Position {
	x, y : Int
} //Describe a position, in X or Y

sig Drone {
    currentPosition : Position one -> Time
} // A drone have a position on the grid 

sig Receptacle {
	position : Position
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

pred go{}

run go

fact soloDrone {  // Two drones can not be on the same position at the same time
    all t : Time | 
	no d0, d1 : Drone |
	d0 != d1 && 
	d0.currentPosition.t = d1.currentPosition.t
}

fact soloReceptacle {
	no r0, r1 : Receptacle |
	r0 != r1 &&
	r0.position = r1.position
}

fact grilleReduite {
	all p : Position | p.x>=0 && p.x<=6 && p.y>=0 && p.y<=6
}

fact soloDeplacement {
	all d : Drone | all t,t1 : Time | t1!=t.next || distanceManhattan[d.currentPosition.t, d.currentPosition.t1] < 2 
}



fun absoluteValue [ a : Int ] : Int {
    a>=0 => a 
    else mul[-1,a] 
}

fun distanceManhattan [ p1, p2 : Position ] : Int {
    plus [ absoluteValue [ minus[p1.x, p2.x] ] ,  absoluteValue [ minus[p1.y, p2.y] ] ]
}

//TODO un receptacle et un entrepot ne peuvent pas etre sur la meme position

/*-----------------------------Ne pas supprimer
pred soloPosition  {
	no p0, p1 : Position |
	p0 != p1 &&
	p0.x = p1.x &&
	p0.y = p1.y
}

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

pred testM {
	some p0, p1 : Position |
	p0.x = 2 &&
	p0.y =2 &&
	p1.x = 1 &&
	p1.y = 1 &&
	distanceManhattan[p0, p1] = 2
}

run testM for 2 but exactly 2 Position
