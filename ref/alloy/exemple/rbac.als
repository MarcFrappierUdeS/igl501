sig Utilisateur {
roles : set Role
}

sig Role {
herite : set Role,
permission : Action -> Objet
}
fact {
no (iden & ^herite)
}

sig Objet {}
sig Action {}

pred Acces[u:Utilisateur, a:Action, o : Objet]
{
a->o in u.roles.*herite.permission
}

fun all_permission[]: Utilisateur->Action->Objet
{
{u:Utilisateur, a:Action, o : Objet | Acces[u,a,o]}
}

one sig U1,U2 extends Utilisateur {}
one sig R1,R2,R3 extends Role {}
one sig O1, O2 extends Objet {}
one sig Lire, Ecrire extends Action {}

fact {
roles = U1->R1
herite = R1->R2 + R2->R3
permission = R1-> Lire -> O1 + R2-> Ecrire -> O2 
}


run {#Utilisateur=2} for 3
