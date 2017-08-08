module construtora

//Entidades
sig Construtora {
	
	pedreiros : set Pedreiro,
	engenheiros : set Engenheiro, 
	pintores : one Pintor

}

sig Pedreiro{
	contratante : one Construtora
}
sig Pintor{
	contratante : one Construtora
}
sig Engenheiro {

	contratante : one Construtora

}
sig EngenheiroCivil extends Engenheiro{}
sig EngenheiroEletricista extends Engenheiro{}


//Fatos
fact EngenheiroCivilOuEletricista {

	Engenheiro = EngenheiroCivil + EngenheiroEletricista

}

fact equipesUnicas {

	all p: Pedreiro | some c:Construtora | p in pedreirosDaConstrutora[c]
	all p:Pintor | some c:Construtora | p in pintoresDaConstrutora[c]
	all e:Engenheiro | some c:Construtora | e in engenheirosDaConstrutora[c]
	

}


fact ConstrutoraSingleton {
	#Construtora = 1

}

//Function

fun pedreirosDaConstrutora[c:Construtora]: set Pedreiro {
	c.pedreiros
}

fun pintoresDaConstrutora[c:Construtora]: one Pintor{
	c.pintores
}

fun engenheirosDaConstrutora[c:Construtora]: set Engenheiro {
	c.engenheiros
}

pred show []{
	

}
run show
