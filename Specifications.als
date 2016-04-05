open GestionCouple

open util/ordering[Time] as to
sig Time {}

sig Batterie {
	unite : Int one ->Time
}

sig Drone {
    currentPosition : Position one -> Time,
	commande : Commande lone -> Time,
	capacite : Int,
	batterie : one Batterie
} // A drone have a position on the grid 

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
	all b : Batterie | all t : Time | b.unite.t <= 3  && b.unite.t >= 0
}//La capacité de la batterie d’un drone est de 3 unités d’énergie.


fact ConsommeEnergie {
	 all d : Drone | all t,t1 : Time | t1!=t.next || d.currentPosition.t = d.currentPosition.t1 || d.batterie.unite.t1 = minus[d.batterie.unite.t,1]
}//Un drone consomme 1 unité d’énergie pour faire 1 pas sur la grille.

fact recharge {
	all d : Drone | all t,t1 : Time | no r : Receptacle | no e : Entrepot |
	 t1!=t.next || 
	d.currentPosition.t != d.currentPosition.t1 ||
	(d.currentPosition.t != r.position && 
	d.currentPosition.t != e.position) ||
	d.batterie.unite.t1 = plus[d.batterie.unite.t,1]
}

/*
fact tropLoin {
	all d : Drone | all t,t1
	"assez d'énergie" || d.currentPosition.t = d.currentPosition.t1


fact droneInactif {
	all d : Drone | all t,t1 : Time | some r : Receptacle | some e : Entrepot |
	 t1!=t.next || 
	d.currentPosition.t != d.currentPosition.t1 ||
	d.currentPosition.t = r.position ||
	d.currentPosition.t = e.position ||
	d.batterie.unite.t1 = d.batterie.unite.t
}
*/

fact grilleReduite {
	all p : Position | p.x>=0 && p.x<=6 && p.y>=0 && p.y<=6
}

fact soloDeplacement {
	all d : Drone | all t,t1 : Time | t1!=t.next || DistanceManhattan[d.currentPosition.t, d.currentPosition.t1] < 2 
}

fact soloCapaDrone {
	all d1, d2 : Drone | d1.capacite = d2.capacite && d1.capacite > 0
}

fact soloCapaRecep {
	all r1, r2 : Receptacle | r1.capacite = r2.capacite && r1.capacite > 0
}

fact commandeNonVide {
	all c: Commande | c.produits > 0
}

fact tailleCommandeDrone {
	all c : Commande | no d : Drone | c.produits > d.capacite
}

fact tailleCommandeRecep {
	all c : Commande | no r : Receptacle | c.produits > r.capacite
}

fact dnb {
	#Drone = 2 && #Batterie = 2
}

fact rnb {
	#Receptacle = 3
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


pred voisin [ p : Position ]{ // voisin : distance de manhattan = 1 unité
   some  r : Receptacle | DistanceManhattan[r.position,p]=1
}

pred voisinEntrepot {
    one e : Entrepot |
	voisin [ e.position ]
}

pred distanceReceptacle { // contrainte 14
	no r1: Receptacle | all r2:Receptacle | ( ( r1!=r2 ) && ( DistanceManhattan [r1.position,r2.position] > 3 ))
}

fact soloBatterie {
	all d1,d2 : Drone | d1=d2 || d1.batterie != d2.batterie
}

fact conserverCommande { // un drone conserve sa commande d'un temps t à t+1 ; Attention, la récupération à l'entrepôt et le dépôt à un récéptacle sont gérés ailleurs
	//all d : Drone | one c : Commande | all t1, t2 : Time | ( t2 = t1.next && d.commande.t1 = c && d.currentPosition.t1 != c.cible.position )=> ( d.commande.t2 = c)
	all d:Drone | all t1,t2 : Time |
	(t2=t1.next && 
	(d.currentPosition.t1 != Entrepot.position || (some c:Commande | d.commande.t1 = c)) &&
	d.currentPosition.t1 != d.commande.t1.cible.position) => d.commande.t1 = d.commande.t2
}

fact chargerCommande {
	all d: Drone |
	all t1, t2 : Time |  
	(	t2 = t1.next && d.currentPosition.t1 = Entrepot.position && (no c1 : Commande | d.commande.t1 = c1)  ) =>( ( some c2 : Commande | d.commande.t2 = c2 ) 
	&& d.currentPosition.t2 = Entrepot.position)
	//	t2 = t1.next && (no c1 : Commande | d.commande.t1 = c1) =>  ( some c2 : Commande | d.commande.t2 = c2 )
}

fact dechargerCommande {
	all d:Drone |
	all t1,t2 : Time |
	(t2=t1.next && 
	 d.currentPosition.t1 = d.commande.t1.cible.position) 
	=> (d.currentPosition.t2 = d.currentPosition.t1 && (no c:Commande | d.commande.t2 = c))
 	 
}

pred unload {
	one d:Drone | one t : Time | t=first  && d.currentPosition.t = d.commande.t.cible.position
}

pred go {
	one d: Drone | one t : Time | t = first && (no c:Commande | d.commande.t = c) && d.currentPosition.t=Entrepot.position
    && unload
}

run go for 5 but exactly 4 Commande, exactly 6 Time
