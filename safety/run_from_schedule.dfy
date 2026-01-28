// /*
//  * Fair schedule
//  */
// datatype Choice = send | arrive | deliver | deliver_minicast
// type Event = (Choice, Process, Process)
// type Schedule = nat -> Event
// ghost predicate IsSchedule(schedule: Schedule, P : set<Process>)
// {
//   forall i :: schedule(i).1 in P // (Choice, Sender, Receiver)
// }

// ghost predicate FairSchedule(schedule: Schedule, P : set<Process>)
// {
//   IsSchedule(schedule, P) &&
//   forall c : Choice, p <- P, q <- P , n : nat :: HasNext(schedule, c, p, q, n)
// }

// ghost predicate HasNext(schedule: Schedule, c: Choice, p: Process, q: Process, n: nat)
// {
//   exists n' :: n <= n' && schedule(n') == (c, p, q)
// }


// method RunFromSchedule(processes: set<Process>, initiator: Process, schedule: nat -> Event)
//   requires forall n :: schedule(n).1 in processes
//   requires forall n :: schedule(n).2 in processes
//   requires FairSchedule(schedule, processes)
//   decreases *
// {
//   var sys := new System(processes);
//   var n := 0;

//   while true
//     invariant sys.Valid()
//     invariant sys.CausallyOrdered()
//     invariant sys.ValidMCs()
//     decreases *
//   {
//     var coin, p, q := schedule(n).0, schedule(n).1, schedule(n).2;
    
//     match coin
//     case send =>
//       var toSend: bool := *;
//       if(toSend && q != p){
//         var m := sys.Send(p, q);
//         sys.SendMinicast(p, q);
//       }
//     case arrive =>
//       if (sys.inTransit[(p, q)] != []) {
//         sys.Arrive(p, q);
//       }
//     case deliver =>
//       if (sys.arrived[(p, q)] != [] && sys.arrived[(p, q)][0].Unicast?) {
//         sys.Deliver(p, q);
//       }
//     case deliver_minicast =>
//       if (sys.arrived[(p, q)] != [] && sys.arrived[(p, q)][0].Minicast?) {
//         sys.DeliverMinicast(p, q);
//       }
//       n := n + 1;
//   }
// }