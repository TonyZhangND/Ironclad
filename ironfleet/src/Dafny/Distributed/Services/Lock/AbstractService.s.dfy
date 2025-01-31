include "../../Common/Framework/AbstractService.s.dfy"

module AbstractServiceLock_s refines AbstractService_s {
export Spec
    provides Native__Io_s, Environment_s, Native__NativeTypes_s
    provides ServiceState 
    provides Service_Init, Service_Next, Service_Correspondence
export All reveals *

datatype ServiceState' = ServiceState'(
    hosts:set<EndPoint>,
    history:seq<EndPoint>
    )

type ServiceState = ServiceState'

ghost predicate Service_Init(s:ServiceState, serverAddresses:set<EndPoint>)
{
       s.hosts == serverAddresses
    && (exists e :: e in serverAddresses && s.history == [e])
}

ghost predicate Service_Next(s:ServiceState, s':ServiceState)
{
       s'.hosts == s.hosts
    && (exists new_lock_holder :: 
            new_lock_holder in s.hosts
         && s'.history == s.history + [new_lock_holder])
}

ghost function Uint64ToBytes(u:uint64) : seq<byte>
{
  [( u/0x1000000_00000000)        as byte,
   ((u/  0x10000_00000000)%0x100) as byte,
   ((u/    0x100_00000000)%0x100) as byte,
   ((u/      0x1_00000000)%0x100) as byte,
   ((u/         0x1000000)%0x100) as byte,
   ((u/           0x10000)%0x100) as byte,
   ((u/             0x100)%0x100) as byte,
   ( u                    %0x100) as byte]
}

ghost function MarshallLockMsg(epoch:int) : seq<byte>
{
  if 0 <= epoch < 0x1_0000_0000_0000_0000 then
        [ 0, 0, 0, 0, 0, 0, 0, 1] // MarshallMesssage_Request magic number
      + Uint64ToBytes(epoch as uint64)        
  else 
      [ 1 ]
}

ghost predicate Service_Correspondence(concretePkts:set<LPacket<EndPoint, seq<byte>>>, serviceState:ServiceState) 
{
    forall p, epoch :: 
        p in concretePkts 
     && p.src in serviceState.hosts 
     && p.dst in serviceState.hosts 
     && p.msg == MarshallLockMsg(epoch) 
     ==>
        1 <= epoch <= |serviceState.history|
     && p.src == serviceState.history[epoch-1]
}

}
