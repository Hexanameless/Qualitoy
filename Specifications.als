open util/ordering[Time] as to
sig Time {
	 value : one Int
}

sig Position {x, y : Int}

sig Drone {
				capacity : Int,
				energie : Int
				 } // A drone have a position on the grid 





sig Receptacle {position : Position, capacity : Int

} //There are receptacle which have a position on the grid 


one sig Entrepot {position : Position,
							 receptaclesVoisins : some Receptacle    	//An Entrepot contains at least one " receptables voisins " (contrainte 13)
							} // There is only one warehouse which have a position on the grid

pred ReceptacleVoisins {
	all e : Entrepot | (e.position.y= e.receptaclesVoisins.position.y && (minus [e.position.x , e.receptaclesVoisins.position.x]=1 ) or ( minus [e.position.x , e.receptaclesVoisins.position.x]=-1 ))
	or ( e.position.x= e.receptaclesVoisins.position.x && ( minus [e.position.y , e.receptaclesVoisins.position.y]=1 ) or (minus [e.position.y , e.receptaclesVoisins.position.y]=1)) 
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

pred go{
	
}

run go

