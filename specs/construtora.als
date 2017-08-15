module construtora



//Entidades
sig Construtora {
	predio: one Predio,
	condominio: one Condominio,
	estadio: one Estadio
}

abstract sig Obra{
	pedreiros: one EquipeDePedreiros
}

one sig Predio extends Obra{
	construtora : one Construtora,
	aptos : set ApartamentoComTresQuartos
}

sig PredioDoCondominio{
	condominio : one Condominio, 
	apartamentos1Quarto: set ApartamentoComUmQuarto,
	apartamentos2Quartos: set ApartamentoComDoisQuartos
}

one sig Condominio extends Obra{
	construtora : one Construtora,
	predios: set PredioDoCondominio
}

one sig Estadio extends Obra{
	construtora : one Construtora,
	fiscal: one FiscalDoEstado
}


sig EquipeDePedreiros {
	obra: lone Obra
}

one sig EquipeDePintores {
	obra : one Obra
}

abstract sig Engenheiro {
	obra : one Obra
}

one sig EngenheiroEletricista extends Engenheiro {}

one sig EngenheiroCivil extends Engenheiro {}

abstract sig Apartamento{
	dono : one Pessoa
}

sig ApartamentoComUmQuarto extends Apartamento {
	predio: one PredioDoCondominio
	
}

sig ApartamentoComDoisQuartos extends Apartamento {
	predio: one PredioDoCondominio
}


sig ApartamentoComTresQuartos extends Apartamento {
	--Esse tipo de apartamento é apenas para prédios	
	predio : one Predio

}

sig Pessoa{
	apartamentos : some Apartamento
}

sig FiscalDoEstado {
	estadio: one Estadio
}
//Funções



fun PrediosDoCondominio[c:Condominio]: set PredioDoCondominio {
	c.predios
} 


//Fatos

fact PrediosDoCondominioTemApartamentos {
 all p: PredioDoCondominio | #p.apartamentos1Quarto = 2 and #p.apartamentos2Quartos = 2
}

fact EquipesDePedreiro {
	#EquipeDePedreiros = 4
	all edp:EquipeDePedreiros | all o:Obra | edp.obra = o => o.pedreiros = edp
}

fact PredioDoCondominioPossuiQuartos {
	all p:PredioDoCondominio | QuantidadeDeQuartos[p]
}

fact TodoPredioDeCondominioTemUmCondominio {

	all p:PredioDoCondominio | some c:Condominio | PredioEstaNoCondominio[p,c]
}

fact QuantidadeDePrediosPorCondominio {
	all c: Condominio| #c.predios = 2	
}

fact TodaPessoaTemPeloMenosUmApartamento {
	all p:Pessoa | temApartamentos[p]
	all ap:Apartamento | all p:Pessoa | apartamentoTemDonoUnico[ap,p]
}

fact quartosDosAptosDoCond {
	all pdc:PredioDoCondominio | all apt:ApartamentoComUmQuarto 
	| (apt in pdc.apartamentos1Quarto) => apt.predio = pdc

	all pdc:PredioDoCondominio | all apt:ApartamentoComDoisQuartos 
	| (apt in pdc.apartamentos2Quartos) => apt.predio = pdc
}

fact PedreirosTrabalhamEmApenasUmObraPorVez {
	all p:EquipeDePedreiros | all o:Obra | pedreirosEmUmaUnicaObra[p,o]
}

fact EngenheirosUnidos {
	all e:EngenheiroEletricista | all c:EngenheiroCivil | e.obra = c.obra 
}

fact EngenheirosSeparadosDosPintores {
	all e:Engenheiro | all p:EquipeDePintores | engenheiroNaoTrabalhaComPintores[e,p]
}

fact estadioTemFiscal {
	all e:Estadio | temFiscal[e]
}

fact numDePredios {
	#PredioDoCondominio = 2
}

fact aptosDoPredio {
	all prd:Predio | #prd.aptos = 8
}

//Predicados

pred QuantidadeDeQuartos[p:PredioDoCondominio]{

	#p.apartamentos1Quarto = 2 <=> #p.apartamentos2Quartos = 2

}

pred PredioEstaNoCondominio[p:PredioDoCondominio, c:Condominio]{
	 p.condominio = c <=> p in c.predios
}

pred temApartamentos[p:Pessoa]{
	some p.apartamentos
}

pred pedreirosEmUmaUnicaObra[p:EquipeDePedreiros, o:Obra]{
	 o.pedreiros = p => p.obra = o
}

pred engenheiroNaoTrabalhaComPintores[e:Engenheiro, p:EquipeDePintores]{
	 e.obra != p.obra
}

pred apartamentoTemDonoUnico[ap:Apartamento, p:Pessoa]{
	ap.dono = p <=> ap in p.apartamentos
}

pred temFiscal[e:Estadio] {
	one e.fiscal
}
pred show []{
	#Construtora = 1	
}


--Asserts 

assert engenheirosTrabalhamSempreJuntos {
	all ee:EngenheiroEletricista | all ec:EngenheiroCivil | ee.obra = ec.obra
}

assert prediosTemApartamentosDeTresQuartos {
	all p:Predio | all ap3q:ApartamentoComTresQuartos | (ap3q in p.aptos) => ap3q.predio = p
}

assert estadioSempreTemFiscal {
	all e:Estadio | all f:FiscalDoEstado | e.fiscal = f => f.estadio = e
}

//check prediosTemApartamentosDeTresQuartos
//check engenheirosTrabalhamSempreJuntos
//check estadioSempreTemFiscal

run show for 4  but 20 Apartamento
