open util/ordering [R] as rs // ordonnancement des ressources
open util/ordering [State] as st // trace des états du système

enum Event {init,acquerir,liberer,stutter}

sig P {} // Processus
sig R {} // Ressources

sig State {
  obj : P -> R,  // objectif : ressources à acquérir par un processus
  acq : P -> R,  // ressources acquises par le processus
  event : Event
}
// à compléter

pred Acquerir[p:P, r:R, s,s':State]
{ ... }

pred Liberer[p:P, s,s':State]
{ ... }

pred Stutter[s,s':State]
{ ... }

pred Init[s:State]
{
all p:P | some p.(s.obj) and no p.(s.acq)
s.event = init
}
