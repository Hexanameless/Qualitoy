open util/integer

sig Receptacle {
    position : Position,
    capacite : Int
} 
//Un receptacle à une position Position a une capacité capacite


sig Position {x, y : Int} 
//Une position est décrite par ses coordonnées en x et en y

sig Couple {
    p1, p2 : one Position,
    r : p1 -> p2
}
//Un couple va représenter des positions successives dans un chemin. La relation r sera utile pour la fermeture transitive
//Notons que le fait PositionRec défini plus loin oblige ces positions à être occupées par l'entrepôt ou un réceptacle

sig Chemin{
    depart,arrivee:one Position,
    value : set Couple
}
//Un chemin est un ensemble de couples dont deux positions sont remarquables: le départ et l'arrivée


one sig Entrepot{position:Position}
//L'entrepôt est unique à une position déterminée


fun AbsoluteValue [ a:Int ] : Int {
    a>=0 => a 
    else mul[-1,a] 
}
//Fonction donnant la valeur absolue d'un nombre


fun DistanceManhattan [ p1,p2 : Position ] : Int {
    plus [ AbsoluteValue [ minus[p1.x, p2.x] ] ,  AbsoluteValue [ minus[p1.y, p2.y] ] ]
}
//Fonction donnant la  distance de manhattan entre deux positions


fact CapaciteRec{
    all r : Receptacle | r.capacite = 5
}
//Tous les receptacles ont une capacité de 5


fact PositionRec{
    all c:Couple | (((one r : Receptacle|r.position=c.p1)||Entrepot.position=c.p1)&&((one r : Receptacle|r.position=c.p2)||Entrepot.position=c.p2))&&(no r : Receptacle|r.position=Entrepot.position)
}
//Aux positions d'un couple, il ne peut y avoir que l'entrepôt ou un unique réceptacle


pred DirectementAccessible [ p1 , p2 : Position ] {
    DistanceManhattan [p1 , p2 ] <= 3 
}
//Deux positions sont directement accessibles si leur distance est inférieure à 3 (autonomie des drones


fact CoupleAcc {
        all c : Couple | DirectementAccessible[c.p1,c.p2]
}
//Les positions d'un couple sont directement accessibles, c'est à dire à moins de 3 cases l'une de l'autre


pred Accessible[p1:Position,p2:Position] {
(    (p1 in (*(Couple.r)).p1)&&    (p2 in (*(Couple.r)).p2))||((p2 in (*(Couple.r)).p1)&&(p1 in (*(Couple.r)).p2))
}
/*Pour déterminer si un drone peut aller de p1 à p2 on utilise la fermeture transitive sur la relation r de couple
p1 doit faire partie du membre gauche de *r et p2 du membre droit
*/


fact ReceptacleAcc{
        all r : Receptacle  |one e:Entrepot|Accessible[r.position,e.position]
}
//Tous les réceptacles sont accessibles de l'entrepot



fact DistinctCouple {
    no c : Couple | c.p1 = c.p2 
}
//Les positions d'un couple sont distinctes



fact SoloPosition{
    no p0, p1 : Position | (p0 != p1) &&
                                    ((p0.x = p1.x) && (p0.y = p1.y))
}
//Les positions sont uniques 


fact SoloCouple{
    no c0, c1 : Couple | ((((c0.p1 = c1.p2) &&
                                    (c0.p2 = c1.p1) )||((c0.p1=c1.p1)&&(c0.p2=c1.p2)))&&c0!=c1)
}
//Les couples sont uniques


fact nbCouple{
    #Couple = #Receptacle
}
//Il y a un couple par receptacle


pred verifDepart[ch:Chemin]{
    (one co:Couple|co in ch.value&&co.p1=ch.depart)&&(no co:Couple|co in ch.value&&co.p2=ch.depart)
}

pred verifArrivee[ch:Chemin]{
    (one co:Couple|co in ch.value&&co.p2=ch.arrivee)&&(no co:Couple|co in ch.value&&co.p1=ch.arrivee)
}
pred verifMilieu[ch:Chemin]{
    (all co:Couple|co in ch.value&&(co.p1=ch.depart||(one co2:Couple |co2 in ch.value&&co2.p2=co.p1))&&(co.p2=ch.arrivee||(one co2:Couple|co2 in ch.value&&co2.p1=co.p2)))
}


fact defChemin{

    all ch:Chemin|verifDepart[ch]&&verifArrivee[ch]&&verifMilieu[ch]

}
/*
A l'aide des prédicats verifDepart, verifArrivee, et verifMilieu, def chemin garantit que:
- Dans le chemin, il n'y a qu'un couple dont la position p1 est la même que le départ,
et aucun dont la position p1 est la même que l'arrivée
- Dans le chemin, il n'y a qu'un couple dont la position p2 est la même que l'arrivée,
et aucun dont la position p2 est la même que le départ
- Dans le chemin, pour chaque couple, soit sa position p1 est la même que le départ,
soit il n'y a qu'un autre couple dont la position p2 est égale à sa position p1
- Dans le chemin, pour chaque couple, soit sa position p2 est la même que l'arrivée,
soit il n'y a qu'un autre couple dont la position p1 est égale à sa position p2
*/


fact uniqueChemin{
   #Chemin = 1
}
//il n'y a qu'un chemin


fact depEntrepot{
    all ch:Chemin|ch.depart=Entrepot.position
}
//L'unique chemin part de l'entrepot



pred go{
     (no p : Position | p.x<0||p.x>4||p.y<0||p.y>4)
}
//prédicat de test



run  go for 10 but exactly 4 Position, exactly 2 Receptacle
