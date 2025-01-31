//- The high-level spec is written in the form of a state-machine
//- The states and transition ghost functions are instantiated on a per-service basis

include "../Native/Io.s.dfy"
include "Environment.s.dfy"

abstract module AbstractService_s {
import opened Native__Io_s
import opened Environment_s 
import opened Native__NativeTypes_s

type ServiceState 

ghost predicate Service_Init(s:ServiceState, serverAddresses:set<EndPoint>) 
ghost predicate Service_Next(s:ServiceState, s':ServiceState) 

ghost predicate Service_Correspondence(concretePkts:set<LPacket<EndPoint, seq<byte>>>, serviceState:ServiceState)

}
