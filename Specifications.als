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

fact soloDrone {  // Deux drônes ne peuvent pas être sur la même position au même moment
    all t : Time | 
	no d0, d1 : Drone |
	d0 != d1 && 
	d0.currentPosition.t = d1.currentPosition.t
}

fact soloDroneParCommande {	// Deux drônes ne peuvent pas avoir la même commande
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

fact  CapBatterie { //La capacité de la batterie d’un drone est de 3 unités d’énergie.
	all b : Batterie | all t : Time | b.unite.t <= 3  && b.unite.t >= 0
}

fact ConsommeEnergie { //Un drone consomme 1 unité d’énergie pour faire 1 pas sur la grille.
	 all d : Drone | all t,t1 : Time | //Pour tout drone, à tout temps  soit : 
	 t1!=t.next || //On ne travaille pas sur deux temps consécutifs 
	d.currentPosition.t = d.currentPosition.t1 || //Avec deux temps consécutifs, la position est tout de même inchangée
	d.batterie.unite.t1 = minus[d.batterie.unite.t,1] //Sinon, le drone a bougé, il perd une unité de batterie.
}

fact recharge { //Un drone recharge 1 unité de batterie par unité de temps s'il reste sur un receptacle ou à l'entrepôt.
	all d : Drone | all t,t1 : Time | //Pour tout drone, à tout temps 
	 no r : Receptacle | no e : Entrepot | //Il n'existe pas de receptacle ou d'entrepot tels que soit : 
	 t1!=t.next ||  //On ne travaille pas sur deux temps consécutifs 
	d.currentPosition.t != d.currentPosition.t1 || //Avec deux temps consécutifs, la position est modifiée
	(d.currentPosition.t != r.position && 
	d.currentPosition.t != e.position) || //Le drone n'a pas bougé mais n'était ni sur un receptacle, ni à l'entrepot
	d.batterie.unite.t = 3 || //Le drone est resté sur un receptacle ou à l'entrepot mais la batterie est déjà pleine
	d.batterie.unite.t1 = plus[d.batterie.unite.t,1] // Sinon, on recharge la batterie de 1 unité.
}

/*
fact tropLoin {
	all d : Drone | all t,t1
	"assez d'énergie" || d.currentPosition.t = d.currentPosition.t1
*/

fact droneInactif {
	all d : Drone | all t,t1 : Time | some r : Receptacle | some e : Entrepot |
	 t1!=t.next || 
	d.currentPosition.t != d.currentPosition.t1 ||
	d.currentPosition.t = r.position ||
	d.currentPosition.t = e.position ||
	d.batterie.unite.t1 = d.batterie.unite.t
}

fact grilleReduite {
	all p : Position | p.x>=0 && p.x<=6 && p.y>=0 && p.y<=6
}

fact soloDeplacement { // Soit un drone se déplace d'une unité, soit il reste immobile
	all d : Drone | all t,t1 : Time | t1!=t.next || DistanceManhattan[d.currentPosition.t, d.currentPosition.t1] < 2 
}

fact soloCapaDrone { // Une seule capacité identique à tous les drônes
	all d1, d2 : Drone | d1.capacite = d2.capacite && d1.capacite > 0
}

fact soloCapaRecep { // Une seule capacité identique à tous les réceptacles
	all r1, r2 : Receptacle | r1.capacite = r2.capacite && r1.capacite > 0
}

fact commandeNonVide {
	all c: Commande | c.produits > 0
}

fact tailleCommandeDrone { // On restreint le système en disant qu'il n'y a pas de commande tel qu'aucun drône ne peut s'en occuper en une fois
	all c : Commande | no d : Drone | c.produits > d.capacite
}

fact tailleCommandeRecep { // Aucun réceptacle n'a une capacité inférieur à une commande
	all c : Commande | no r : Receptacle | c.produits > r.capacite
}

fact dnb {
	#Drone = 3 && #Batterie = 3
}

fact rnb {
	#Receptacle = 3
}

fact entrepotDiffReceptacle { // Un receptacle et un entrepot ne peuvent pas etre sur la meme position
	no e : Entrepot | some r1 : Receptacle | e.position = r1.position
}

fact soloPosition  { // Les positions sur la grille sont toutes distinctes
	no p0, p1 : Position |
	p0 != p1 &&
	(p0.x = p1.x &&
	p0.y = p1.y)
}

pred voisin [ p : Position ]{ // Voisin : distance de manhattan = 1 unité
   some  r : Receptacle | DistanceManhattan[r.position,p]=1
}

pred voisinEntrepot {
    one e : Entrepot |
	voisin [ e.position ]
}

fact conserverCommande { // un drone conserve sa commande d'un temps t à t+1 ; Attention, la récupération à l'entrepôt et le dépôt à un récéptacle sont gérés ailleurs
    all d:Drone | all t1,t2 : Time |
    (t2=t1.next && 
    (d.currentPosition.t1 != Entrepot.position || (some c:Commande | d.commande.t1 = c)) &&
    d.currentPosition.t1 != d.commande.t1.cible.position) => d.commande.t1 = d.commande.t2
}

// Ne fonctionne pas tout le temps
fact chargerCommande { // Si au temps t, le drône d1 n'a pas de commande et se trouve sur l'entrepôt, alors à t+1 il prend une commande et reste sur l'entrepôt
    all d: Drone |
    all t1, t2 : Time |  
    (    t2 = t1.next && d.currentPosition.t1 = Entrepot.position && (no c1 : Commande | d.commande.t1 = c1)  ) =>( ( some c2 : Commande | d.commande.t2 = c2 ) 
    && d.currentPosition.t2 = Entrepot.position)

// Ne fonctionne pas
fact dechargerCommande { // Si au temps t, le drône se trouve sur un récepacle et a une commande, alors à t+1 il décharge sa commande et reste sur le réceptacle
    all d:Drone |
    all t1,t2 : Time |
    (t2=t1.next && 
     d.currentPosition.t1 = d.commande.t1.cible.position) 
    => (d.currentPosition.t2 = d.currentPosition.t1 && (no c:Commande | d.commande.t2 = c))
     
}

fact soloBatterie { // Chaque drône a sa propre batterie
	all d1,d2 : Drone | d1=d2 || d1.batterie != d2.batterie
}

pred go{}
run go for 4 but 10 Position, 6 Time
