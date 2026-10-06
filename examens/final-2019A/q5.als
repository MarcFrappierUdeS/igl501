sig Classe {
ext : lone Classe,
methodes : Methode -> Corps
}

sig Methode {}

sig Corps {}

sig Objet {
type : Classe
}

fact {
all c : Classe | c.methodes in Methode lone -> lone Corps
no iden & ^ext // pas de cycle
}

pred herite[o:Objet,c:Classe,m:Methode]
{
    c in o.type.*ext
and m in c.methodes.Corps
}

pred plusSpecifique[c,c':Classe]
{
c' in c.^ext
}

fun executer[o : Objet, m : Methode]: Corps
{
  { b : Corps |
      some c : Classe | herite[o,c,m] and b = m.(c.methodes) and
        no c' : Classe | herite[o,c',m] and plusSpecifique[c',c]
  }
}

one sig C1,C2,C3 extends Classe {}
one sig M1,M2,M3 extends Methode {}
one sig B1,B2,B3,B4,B5 extends Corps {}
one sig O1 extends Objet {}

run test {
ext = C3 -> C2 + C2 -> C1
methodes =
  C1 -> M1 -> B1
+ C1 -> M2 -> B2
+ C2 -> M1 -> B3
+ C2 -> M2 -> B4
+ C3 -> M1 -> B5
type = O1 -> C3 
} for 3 

