 
 sig Position {x, y : Int
 					} //Describe a position, in X or Y
 
sig Couple {
	p1, p2 : Position
}

fun AbsoluteValue [ a:Int ] : Int {
	a>=0 => a 
	else mul[-1,a] 
}

fun DistanceManhattan [ p1,p2 : Position ] : Int {
	plus [ AbsoluteValue [ minus[p1.x, p2.x] ] ,  AbsoluteValue [ minus[p1.y, p2.y] ] ]
}

fun DirectementAccessible [ p1 , p2 : Position ] : Int {
	DistanceManhattan [p1 , p2 ] <= 3 => 1
	else 0
}

fun ListDirectement  : set Couple {
  	 {c : Couple |
	DirectementAccessible [c.p1, c.p2] = 1}
} 
 
fun EstAccessible [   p : Position ] : set Position {
	 
	
}

pred DistinctCouple {
	no c : Couple | c.p1 = c.p2 
}

 pred SoloPosition{//Two Position have different coordinates
 	no p0, p1 : Position | (p0 != p1) &&
 									((p0.x = p1.x) && (p0.y = p1.y))
 }

 pred SoloCouple{//Two Couples have different Positions
 	no c0, c1 : Couple | ((c0.p1 = c1.p2) &&
 									(c0.p2 = c1.p1) )||((c0.p1=c1.p1)&&(c0.p2=c1.p2)&&c0!=c1)
 }

 pred go{
 	(all c : Couple  |  c in ListDirectement) && DistinctCouple //&& SoloPosition && SoloCouple
} 

 
 run go for 5 but  exactly 5 Position
