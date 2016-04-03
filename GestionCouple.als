sig Receptacle {
	position : Position,
	capacite : Int
} 
 sig Position {x, y : Int} //Describe a position, in X or Y
 
sig Couple {
	p1, p2 : one Position,
	r : p1 -> p2
}

one sig Entrepot{p:Position}

fun AbsoluteValue [ a:Int ] : Int {
	a>=0 => a 
	else mul[-1,a] 
}

fun DistanceManhattan [ p1,p2 : Position ] : Int {
	plus [ AbsoluteValue [ minus[p1.x, p2.x] ] ,  AbsoluteValue [ minus[p1.y, p2.y] ] ]
}

fact CapaciteRec{
	all r : Receptacle | r.capacite = 5
}

fact PositionRec{
	all c:Couple | (((one r : Receptacle|r.position=c.p1)||Entrepot.p=c.p1)&&((one r : Receptacle|r.position=c.p2)||Entrepot.p=c.p2))&&(no r : Receptacle|r.position=Entrepot.p)
}

pred DirectementAccessible [ p1 , p2 : Position ] {
	DistanceManhattan [p1 , p2 ] <= 3 
}

pred Accessible[p1:Position,p2:Position] {
(	(p1 in (*(Couple.r)).p1)&&	(p2 in (*(Couple.r)).p2))||((p2 in (*(Couple.r)).p1)&&(p1 in (*(Couple.r)).p2))
}

fact ReceptacleAcc{
		all r : Receptacle  |one e:Entrepot|Accessible[r.position,e.p]
}

fact CoupleAcc {
		all c : Couple | DirectementAccessible[c.p1,c.p2]
}
fact DistinctCouple {
	no c : Couple | c.p1 = c.p2 
}

 fact SoloPosition{//Two Position have different coordinates
 	no p0, p1 : Position | (p0 != p1) &&
 									((p0.x = p1.x) && (p0.y = p1.y))
 }
 fact SoloCouple{
 	no c0, c1 : Couple | ((((c0.p1 = c1.p2) &&
 									(c0.p2 = c1.p1) )||((c0.p1=c1.p1)&&(c0.p2=c1.p2)))&&c0!=c1)
 }


fact nbCouple{
	#Couple = #Receptacle
}
pred go{
	 (no p : Position | p.x<0||p.x>4||p.y<0||p.y>4)
}
 run  go for 10 but exactly 5 Position, exactly 2 Receptacle
