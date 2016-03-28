open util/ordering[Time] as to
sig Time {
	 value : one Int
}

sig Position {x, y : Int,
	d : lone Drone,
	r : lone Receptacle,
	t : one Time,
	e : lone Entrepot
} //Describe a position, in X or Y

sig Drone {
				capacity : Int,
				energie : Int
				 } // A drone have a position on the grid 

one sig Entrepot {} // There is only one warehouse which have a position on the grid

sig Receptacle {
	capacity : Int
} //There are receptacle which have a position on the grid



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

pred go {
	AllReceptacleSomewhere&&OneEntrepot&&NoReceptacleAtEntrepot&&defTime&&capPos
}

run defTime for 4


