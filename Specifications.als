open util/ordering[Time] as to
sig Time {}

sig Position {x, y : Int
                    } //Describe a position, in X or Y

sig Drone {position : Position,
                capacity : Int,
                energie : Int,
                currentPosition : Position one -> Time
                 } // A drone have a position on the grid 


sig Receptacle {position : Position} //There are receptacle which have a position on the grid 


one sig Entrepot {position : Position
                               // receptaclesVoisins : some Receptacle        //An Entrepot contains at least one " receptables voisins " (contrainte 13)
                            } // There is only one warehouse which have a position on the grid

fact soloDrone  // Two drones can not be on the same position at the same time
{
    all t :Time |  no d0, d1 : Drone | (d0 != d1) &&
                                    (d0.currentPosition.t = d1.currentPosition.t)                                                
}

pred ReceptacleVoisin [ p : Position ]{ // voisin : distance de manhattan = 1 unité
   some  r : Receptacle | (p.y= r.position.y && ((minus [p.x , r.position.x]=1 ) or ( minus [p.x , r.position.x]=-1 )))
    or ( p.x= r.position.x && (( minus [p.y , r.position.y]=1 ) or (minus [p.y , r.position.y]=1))) 
}

fun AbsoluteValue [ a:Int ] : Int {
    a>=0 => a 
    else mul[-1,a] 
}

fun DistanceManhattan [ p1,p2 : Position ] : Int {
    plus [ AbsoluteValue [ minus[p1.x, p2.x] ] ,  AbsoluteValue [ minus[p1.y, p2.y] ] ]
}

/*fun EstAccessible [ p : Position ] : Int {
    one e : Entrepot | ( DistanceManhattan [e.position,  p ] = 1 
}*/

pred TestManhattan {
    all r1: Receptacle |(( one r2 : Receptacle |  DistanceManhattan [r1.position , r2.position] = 2)||( one e: Entrepot | DistanceManhattan [r1.position , e.position]=1))
}



pred VoisinEntrepot {
    all e : Entrepot | ReceptacleVoisin [ e.position ]
} 
