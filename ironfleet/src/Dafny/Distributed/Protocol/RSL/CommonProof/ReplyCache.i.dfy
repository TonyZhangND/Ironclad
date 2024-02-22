include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Actions.i.dfy"
include "Constants.i.dfy"
include "PacketSending.i.dfy"

/////////////////////
// INVARIANTS
/////////////////////

module CommonProof__ReplyCache_i {

import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Message_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened Concrete_NodeIdentity_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened CommonProof__PacketSending_i
import opened Temporal__Temporal_s
import opened Environment_s

ghost predicate ReplyCacheObjectInv(cache:ReplyCache, client:NodeIdentity)
{
  client in cache ==> cache[client].Reply? && cache[client].client == client
}

ghost predicate ReplyCacheStateInv(ps:RslState, client:NodeIdentity)
{
  forall idx :: 0 <= idx < |ps.replicas| ==> ReplyCacheObjectInv(ps.replicas[idx].replica.executor.reply_cache, client)
}

lemma lemma_ReplyCacheStateInv(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  client:NodeIdentity
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  ensures  ReplyCacheStateInv(b[i], client)
{
  if i > 0
  {
    lemma_ReplyCacheStateInv(b, c, i-1, client);
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    var ps := b[i-1];
    var ps' := b[i];
    assert RslNext(ps, ps');
    forall idx | 0 <= idx < |ps'.replicas|
      ensures ReplyCacheObjectInv(ps'.replicas[idx].replica.executor.reply_cache, client)
    {
      lemma_ReplicasSize(b, c, i-1);
      lemma_ReplicasSize(b, c, i);

      var s := ps.replicas[idx].replica;
      var s' := ps'.replicas[idx].replica;
      var cache := s.executor.reply_cache;
      var cache' := s'.executor.reply_cache;

      if cache' == cache
      {
        assert ReplyCacheObjectInv(cache', client);
      }
      else
      {
        var ios :| RslNextOneReplica(ps, ps', idx, ios);
        assert ReplyCacheObjectInv(cache', client);
      }
    }
  }
}

}
