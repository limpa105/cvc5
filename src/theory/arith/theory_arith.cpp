/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic theory.
 */

#include "theory/arith/theory_arith.h"

#include "options/smt_options.h"
#include "printer/smt2/smt2_printer.h"
#include "proof/proof_checker.h"
#include "cvc5/cvc5_proof_rule.h"
#include "smt/logic_exception.h"
#include "theory/arith/arith_evaluator.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/equality_solver.h"
#include "theory/arith/linear/theory_arith_private.h"
#include "theory/arith/nl/nonlinear_extension.h"
#include "theory/arith/local_search/local_search_extension.h"
#include "theory/ext_theory.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/cocoa_globals.h"
#include "theory/decision_manager.h"
#include <random>

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {

TheoryArith::TheoryArith(Env& env, OutputChannel& out, Valuation valuation)
    : Theory(THEORY_ARITH, env, out, valuation),
      d_ppRewriteTimer(
          statisticsRegistry().registerTimer("theory::arith::ppRewriteTimer")),
      d_astate(env, valuation),
      d_im(env, *this, d_astate),
      d_ppre(d_env),
      d_bab(env, d_astate, d_im, d_ppre),
      d_eqSolver(nullptr),
      d_internal(new linear::TheoryArithPrivate(*this, env, d_bab)),
      d_nonlinearExtension(nullptr),
      d_localSearchExtension(nullptr),
      d_opElim(d_env),
      d_arithPreproc(env, d_im, d_pnm, d_opElim),
      d_rewriter(nullptr),
      d_arithModelCacheSet(false),
      d_checker()
{
#ifdef CVC5_USE_COCOA
  // must be initialized before using CoCoA.
  initCocoaGlobalManager();
#endif /* CVC5_USE_COCOA */
  // indicate we are using the theory state object and inference manager
  d_theoryState = &d_astate;
  d_inferManager = &d_im;

  // construct the equality solver
  d_eqSolver.reset(new EqualitySolver(env, d_astate, d_im));
  d_rewriter.reset(new ArithRewriter(d_opElim));
}

TheoryArith::~TheoryArith(){
  delete d_internal;
}

TheoryRewriter* TheoryArith::getTheoryRewriter() { return d_rewriter.get(); }

ProofRuleChecker* TheoryArith::getProofChecker() { return &d_checker; }

bool TheoryArith::needsEqualityEngine(EeSetupInfo& esi)
{
  // if the equality solver is enabled, then it is responsible for setting
  // up the equality engine
  return d_eqSolver->needsEqualityEngine(esi);
}
void TheoryArith::finishInit()
{
  const LogicInfo& logic = logicInfo();
  if (logic.isTheoryEnabled(THEORY_ARITH) && logic.areTranscendentalsUsed())
  {
    // witness is used to eliminate square root
    d_valuation.setUnevaluatedKind(Kind::WITNESS);
    // we only need to add the operators that are not syntax sugar
    d_valuation.setUnevaluatedKind(Kind::EXPONENTIAL);
    d_valuation.setUnevaluatedKind(Kind::SINE);
    d_valuation.setUnevaluatedKind(Kind::PI);
  }
  // only need to create nonlinear extension if non-linear logic
  if (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear())
  {
    d_nonlinearExtension.reset(new nl::NonlinearExtension(d_env, *this));
  }

  if (options().arith.localSearchExt)
  {
    d_localSearchExtension.reset(new local_search::LocalSearchExtension(d_env, *this));
  }

  d_eqSolver->finishInit();
  // finish initialize in the old linear solver
  d_internal->finishInit();

  // Set the congruence manager on the equality solver. If the congruence
  // manager exists, it is responsible for managing the notifications from
  // the equality engine, which the equality solver forwards to it.
  d_eqSolver->setCongruenceManager(d_internal->getCongruenceManager());
}

void TheoryArith::preRegisterTerm(TNode n)
{
  
  if (d_localSearchExtension != nullptr)
  {
    Trace("arith") << "Local Search Start 3" << endl;
    localSearchTime.start();
    d_localSearchExtension->preRegisterTerm(n);
    localSearchTime.stop();
  }
  // handle logic exceptions
  Kind k = n.getKind();
  if (k == Kind::POW)
  {
    std::stringstream ss;
    ss << "The exponent of the POW(^) operator can only be a positive "
          "integral constant below "
       << (expr::NodeValue::MAX_CHILDREN + 1) << ". ";
    ss << "Exception occurred in:" << std::endl;
    ss << "  " << n;
    throw LogicException(ss.str());
  }
  bool isTransKind = isTranscendentalKind(k);
  // note that we don't throw an exception for non-linear multiplication in
  // linear logics, since this is caught in the linear solver with a more
  // informative error message
  if (isTransKind || k == Kind::IAND || k == Kind::POW2)
  {
    if (d_nonlinearExtension == nullptr)
    {
      std::stringstream ss;
      ss << "Term of kind " << k
         << " requires the logic to include non-linear arithmetic";
      throw LogicException(ss.str());
    }
    // logic exceptions based on the configuration of nl-ext: if we are a
    // transcendental function, we require nl-ext=full.
    if (isTransKind)
    {
      if (options().arith.nlExt != options::NlExtMode::FULL)
      {
        std::stringstream ss;
        ss << "Term of kind " << k
           << " requires nl-ext mode to be set to value 'full'";
        throw LogicException(ss.str());
      }
    }
    if (options().arith.nlCov && !options().arith.nlCovForce)
    {
      std::stringstream ss;
      ss << "Term of kind " << k
         << " is not compatible with using the coverings-based solver. If "
            "you know what you are doing, "
            "you can try --nl-cov-force, but expect crashes or incorrect "
            "results.";
      throw LogicException(ss.str());
    }
  }
  if (d_nonlinearExtension != nullptr)
  {
    d_nonlinearExtension->preRegisterTerm(n);
  }
  d_internal->preRegisterTerm(n);
}

void TheoryArith::notifySharedTerm(TNode n)
{
  //n = n.getKind() == Kind::TO_REAL ? n[0] : n;
  //d_internal->notifySharedTerm(n);
}

TrustNode TheoryArith::ppRewrite(TNode atom, std::vector<SkolemLemma>& lems)
{
  CodeTimer timer(d_ppRewriteTimer, /* allow_reentrant = */ true);
  Trace("arith::preprocess") << "arith::ppRewrite() : " << atom << endl;
  Assert(d_env.theoryOf(atom) == THEORY_ARITH);
  // Eliminate operators. Notice we must do this here since other
  // theories may generate lemmas that involve non-standard operators. For
  // example, quantifier instantiation may use TO_INTEGER terms; SyGuS may
  // introduce non-standard arithmetic terms appearing in grammars.
  // call eliminate operators. In contrast to expandDefinitions, we eliminate
  // *all* extended arithmetic operators here, including total ones.
  return d_arithPreproc.eliminate(atom, lems, false);
}

TrustNode TheoryArith::ppStaticRewrite(TNode atom)
{
  
  Trace("arith::preprocess") << "arith::ppStaticRewrite() : " << atom << endl;
  Kind k = atom.getKind();
  if (k == Kind::EQUAL)
  {
    return d_ppre.ppRewriteEq(atom);
  }
  else if (k == Kind::GEQ)
  {
    // try to eliminate bv2nat from inequalities
    Node atomr = ArithRewriter::rewriteIneqToBv(atom);
    if (atomr != atom)
    {
      return TrustNode::mkTrustRewrite(atom, atomr);
    }
  }
  return TrustNode::null();
}

Theory::PPAssertStatus TheoryArith::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  return d_internal->ppAssert(tin, outSubstitutions);
}

void TheoryArith::ppStaticLearn(TNode n, NodeBuilder& learned)
{

  if (options().arith.arithStaticLearning)
  {
    d_internal->ppStaticLearn(n, learned);
  }
}

bool TheoryArith::preCheck(Effort level)
{
  Trace("arith-check") << "TheoryArith::preCheck " << level << std::endl;
  return false;
  // if (d_localSearchExtension != nullptr)
  // {
  //   if(!(d_localSearchExtension->postCheck(level)) ){
  //     return false;
  //   }
  // else {
  // Trace("arith") << "local search could not find a solution so we defaulted to simplex" << endl;
  // // std::vector<std::tuple<TNode, bool, TNode>> dls_conflict3 = d_localSearchExtension->getTrivialConflict(false);
  // // AlwaysAssert(dls_conflict3.size()!=0);
  // // for (int i=0; i< dls_conflict3.size(); i++){
  // //       d_internal->preNotifyFact(std::get<0>(dls_conflict3[i]), std::get<1>(dls_conflict3[i]), std::get<2>(dls_conflict3[i]));
  // //     }
  // return  d_internal->preCheck(level);
  // }
  // }
  return d_internal->preCheck(level);
}

void TheoryArith::postCheck(Effort level)
{

  std::cout << "postChecking" << level << endl;
  //std::cout << level << "\n";
  d_im.reset();
  if (level == Theory::EFFORT_LAST_CALL)
  {
    // If we computed lemmas in the last FULL_EFFORT check, send them now.
    if (d_im.hasPendingLemma())
    {
      d_im.doPendingFacts();
      d_im.doPendingLemmas();
      d_im.doPendingPhaseRequirements();
    }
    return;
  }
  if (d_localSearchExtension != nullptr && Theory::fullEffort(level))
  {
      if (!(d_localSearchExtension->postCheck(level))){
        return;
      }
      std::cout << "Starting conflicts\n";
      // DO OPTIONAL CONFLICT NOW :) 
      std::vector<std::tuple<TNode, bool, TNode>> conflict;
      conflict = d_localSearchExtension->getTrivialConflict(level);
      NodeManager* nm = NodeManager::currentNM();
      std::cout << conflict.size() << "\n";
      // AlwaysAssert(facts.size()!=0);
      std::vector<Node> d_conflict{};
      for (const auto& t : conflict) {
       constexpr size_t num_elements = std::tuple_size<typename std::remove_reference<decltype(t)>::type>::value;
            if (num_elements < 3) {
                std::cerr << "Tuple does not contain enough elements.\n";
                std:cout << num_elements << "\n";
                continue; // Skip this iteration
            }
        d_conflict.push_back(std::get<2>(t)); // Index 2 corresponds to the third element
    }
      std::cout << "Got conflict back\n";
       Node body = nm->mkNode(Kind::AND, d_conflict);
      if (d_conflict_guard.size() > 1)
      {
        Trace("arith") << "We did it! Optional Conflicts work\n";
      }
      if (d_conflict_guard.count(body) > 0)
      {
        bool value;
        Node guard = d_conflict_guard[body];
        if (d_astate.getValuation().hasSatValue(guard, value))
        {
          if (value)
          {
               std::cout << "guard was set to true, this should never happen\n";
          }
        SkolemManager* sm = nm->getSkolemManager();
        Node sk = sm->mkDummySkolem("CeLiteral" + std::to_string(d_conflict_guard.size()), nm->booleanType());
        Node lit = d_astate.getValuation().ensureLiteral(sk);
        d_im.addPendingPhaseRequirement(lit, true);
        DecisionStrategy* ds = new DecisionStrategySingleton(
            d_env, "CeLiteral", lit, d_astate.getValuation());
        d_im.getDecisionManager()->registerStrategy(
            DecisionManager::STRAT_LOCAL_SEARCH_GUARD, ds);
        Node lem = nm->mkNode(Kind::OR, lit.negate(), body.negate());
        bool added = d_im.lemma(
            lem, InferenceId::CONFLICT_REWRITE_LIT, LemmaProperty(0));
        d_conflict_guard[lit] = body;
         Node restartVar = sm->mkDummySkolem(
            "restartVar" + std::to_string(d_conflict_guard.size()),
            nm->booleanType(),
            "A boolean variable asserted to be true to force a restart");
        d_im.lemma(restartVar, InferenceId::ARITH_DEMAND_RESTART, LemmaProperty(0));
        return;

          // else
          // {
          //   AlwaysAssert(false) << "guard was set to false, this should not "
          //                          "happen for these examples";
          // }
        }
        else
        {
          AlwaysAssert(false) << "guard has no value, this should never happen";
        }
      }
      else
      {
        SkolemManager* sm = nm->getSkolemManager();
        Node sk = sm->mkDummySkolem("CeLiteral", nm->booleanType());
        Node lit = d_astate.getValuation().ensureLiteral(sk);
        d_im.addPendingPhaseRequirement(lit, true);
        DecisionStrategy* ds = new DecisionStrategySingleton(
            d_env, "CeLiteral", lit, d_astate.getValuation());
        d_im.getDecisionManager()->registerStrategy(
            DecisionManager::STRAT_LOCAL_SEARCH_GUARD, ds);
        Node lem = nm->mkNode(Kind::OR, lit.negate(), body.negate());
        bool added = d_im.lemma(
            lem, InferenceId::CONFLICT_REWRITE_LIT, LemmaProperty(0));
        d_conflict_guard[body] = lit;
        Node restartVar = sm->mkDummySkolem(
            "restartVar"+std::to_string(d_conflict_guard.size()),
            nm->booleanType(),
            "A boolean variable asserted to be true to force a restart");
        d_im.lemma(restartVar, InferenceId::ARITH_DEMAND_RESTART, LemmaProperty(0));
        return;
      }
    

    // localSearchTime.stop();
    // Trace("arith") << "Simplex start 2" << endl;
    // simplexTime.start();
    // for (int i=0; i< static_cast<int>(dls_conflict.size()); i++){
    //     d_internal->preNotifyFact(std::get<0>(dls_conflict[i]), std::get<1>(dls_conflict[i]), std::get<2>(dls_conflict[i]));
    //   }
    // if (d_internal -> postCheck(Theory::EFFORT_STANDARD)){
    //   Trace("arith") << "Simplex found a conflict in smart conflicts" << endl;
    //   simplexTime.stop();
    //   return;
    // };
    // Trace("arith") << "Simplex DID NOT find a conflict in smart conflicts" << endl;
    // std::vector<std::tuple<TNode, bool, TNode>> dls_conflict2 = d_localSearchExtension->getTrivialConflict(level);
    // for (int i=0; i< dls_conflict2.size(); i++){
    //     d_internal->preNotifyFact(std::get<0>(dls_conflict2[i]), std::get<1>(dls_conflict2[i]), std::get<2>(dls_conflict2[i]));
    // }

    //std::cout << "Starting local search\n";
    // localSearchTime.start();
    // if (!d_localSearchExtension->postCheck(level)){
    //   std::cout << "Local search found an assignment\n";
    //    localSearchTime.stop();
    //    return;
    //  } 
    // localSearchTime.stop();
    // std::vector<std::tuple<TNode, bool, TNode>> dls_conflict = d_localSearchExtension->conflict();
    // std::vector<int> conflict_ids;
    // //goto trivial_conflict;
    //  bool lookedAtSmart = true; 
    // if (dls_conflict.size() <= 10){
    //   lookedAtSmart = false;
    //   //goto trivial_conflict;
    // }
    // for( auto triple: dls_conflict){
    //   conflict_ids.push_back(std::get<2>(triple).getId());
    // }
    // std::sort(conflict_ids.begin(), conflict_ids.end());
    // if (!previous_conflicts_ids.insert(conflict_ids).second) {
    //     std::cout << "This conflict has already been seen..." << std::endl;
    //     lookedAtSmart = false;
    //    // goto trivial_conflict;
    // } 
    //Node body =  std::get<2>(dls_conflict[0]);
    //NodeManager* nm = NodeManager::currentNM();
    // for (int i =1 ; i<dls_conflict.size(); i++){
    //       body = nm->mkNode(Kind::AND, body, std::get<2>(dls_conflict[i]));
    //    }
    //d_im.conflict(body, InferenceId::LOCAL_SEARCH_LEMMA);
    //return;
    
      // std::cout << "Body:" << body << "\n";

    
    //else {
      //localSearchTime.stop();
      // simplexTime.start();


      // d_im.clearPending();
      // d_im.clearWaitingLemmas();
      // //d_internal->notifyRestart();
      // // Step 1: Get conflict 
      // // TODO rewrite this to be cleaner 
      // //std::vector<std::tuple<TNode, bool, TNode>> dls_conflict = d_localSearchExtension->conflict();
      //  for (auto i: dls_conflict ){
      //   d_internal->preNotifyFact(std::get<0>(i), std::get<1>(i), std::get<2>(i));
      //  }
      //d_internal->presolve();
      // if (d_internal->postCheck(Theory::EFFORT_STANDARD)){
      // //   // simplex found a real conflict :) 
      //   simplexTime.stop();
      //   std::cout << "simplex found a conflict in smart\n";
      //    return;
      // }
      // if (d_im.hasSent()){
      //   std::cout << "d_im.hasSent()\n";
      //   return;
      // } else {
      //   //d_internal->notifyRestart();
      //    std::cout << "simplex did not find a conflict in smart\n";
      //     std::vector<std::tuple<TNode, bool, TNode>> dls_conflict2 = d_localSearchExtension->getTrivialConflict(lookedAtSmart);
      //    simplexTime.start();
      //    for (auto i: dls_conflict2 ){
      //    d_internal->preNotifyFact(std::get<0>(i), std::get<1>(i), std::get<2>(i));
      //    }
    return;
    } else {
    // std::random_device rd;
    // std::mt19937 gen(rd());
    // std::uniform_int_distribution<> distrib(0, 1);
    // int random_number = distrib(gen);
    // //int size = d_localSearchExtension->getClauseNumber();
    // // if (random_number == 0){
    // // Trace("arith") << "Local Search Start 2" << endl;
    // // localSearchTime.start();
    // // if (size<500 && !(d_localSearchExtension->postCheck(level))){
    // //   localSearchTime.stop();
    // //    return;
    // //   }
    // // localSearchTime.stop();
    // //  }
    // Trace("arith") << "Simplex attempting to find conflict in total conflicts" << endl;
    //  std::vector<std::tuple<TNode, bool, TNode>> dls_conflict3 = d_localSearchExtension->getTrivialConflict(level);
    //  Trace("arith") << "Simplex start 1" << endl;
    // simplexTime.start();
    // for (int i=0; i< dls_conflict3.size(); i++){
    //     d_internal->preNotifyFact(std::get<0>(dls_conflict3[i]), std::get<1>(dls_conflict3[i]), std::get<2>(dls_conflict3[i]));
    //   }
    // // bool result = d_internal->postCheck(level);
    // // if (result) {
    // //    Trace("arith") << "Simplex found a conflict" << endl;
    // // } else {
    // //   Trace("arith") << "Simplex did NOT find a conflict" << endl;
    // //}
    // }
        //d_internal->presolve();
        if (d_internal->postCheck(level))
          {
             Trace("arith") << "Simplex found a conflict" << endl;
             simplexTime.stop();
            //std::cout << "simplex found a conflict in trivial...\n";
            return;
          }
          simplexTime.stop();
          //std::cout << "simplex did not find a conflict in trivial...\n";
        if (d_im.hasSent()){
          Trace("arith") << "Simplex sent something" << endl;
          //std::cout << "d_im.hasSent()\n";
          return;
        }

    
  if (Theory::fullEffort(level))
  {
    d_arithModelCache.clear();
    d_arithModelCacheIllTyped.clear();
    d_arithModelCacheSubs.clear();
    d_arithModelCacheSet = false;
    std::set<Node> termSet;
    if (d_nonlinearExtension != nullptr)
    {
      updateModelCache(termSet);
      // Check at full effort. This may either send lemmas or otherwise
      // buffer lemmas that we send at last call.
      d_nonlinearExtension->checkFullEffort(d_arithModelCache, termSet);
      // if we already sent a lemma, we are done
      if (d_im.hasSent())
      {
        return;
      }
    }
    else if (d_internal->foundNonlinear())
    {
      // set incomplete
      d_im.setModelUnsound(IncompleteId::ARITH_NL_DISABLED);
    }
    // If we won't be doing a last call effort check (which implies that
    // models will be computed), we must sanity check the integer model
    // from the linear solver now. We also must update the model cache
    // if we did not do so above.
    if (d_nonlinearExtension == nullptr)
    {
      updateModelCache(termSet);
    }
    sanityCheckIntegerModel();
    // Now, finalize the model cache, which constructs a substitution to be
    // used for getEqualityStatus.
    finalizeModelCache();
    }
        //d_internal->postCheck(level);
        //simplexTime.stop();
        //return;
      //}
      // Node body = dls_conflict[0];
      // for (int i =1 ; i<dls_conflict.size(); i++){
      //    body = nm->mkNode(Kind::AND, body, dls_conflict[i]);
      // }
      // std::cout << "Body:" << body << "\n";

      // // Step 2: Check if conflict already exists 
      // if (d_conflict_guard.count(body) > 0){
      //   AlwaysAssert(false);
      // bool value;
      // Node guard = d_conflict_guard[body];
      // if (d_astate.getValuation().hasSatValue(guard, value))
      // {
      //   if (value){
      //     // This should never happen 
      //     std::cout << "guard was set to true\n";
      //   }
      //   else {
      //     // This means the guard did not work for some reason
      //     std::cout << "guard was set to false\n";
      //   }
      // } else {
      //   AlwaysAssert(false);
      // }
      // }
      // This conflict has already been seen so we need a new one: randomly choose one 
      // literal to exclude from the body  
      // SkolemManager* sm = nm->getSkolemManager();
      // Node sk = sm->mkDummySkolem("CeLiteral", nm->booleanType());
      // Node lit = d_astate.getValuation().ensureLiteral(sk);
      // //d_im.preferPhase(lit, true);
      // //d_im.doPendingPhaseRequirements();
      // //std::cout << d_astate.getValuation().getModel() << "\n";
      // //DecisionStrategy* ds = new DecisionStrategySingleton(
      // //d_env, "CeLiteral", lit, d_astate.getValuation());
      // //d_im.getDecisionManager() -> registerStrategy(DecisionManager::STRAT_QUANT_CEGQI_FEASIBLE, ds, DecisionManager::STRAT_SCOPE_CTX_INDEPENDENT);
      // //Node lem = nm->mkNode(Kind::OR, lit.negate(), body.negate()); 
      // //d_im.conflict(body, InferenceId::LOCAL_SEARCH_LEMMA);
      // //d_conflict_guard[body] = lit;
      // //std::cout << "Got a conflict\n";
    //}
  }
  //}
  //simplexTime.start();
  Trace("arith") << "TheoryArith::postCheck " << level << std::endl;
  if (Theory::fullEffort(level))
  {
    // Make sure we don't have old lemmas floating around. This can happen if we
    // didn't actually reach a last call effort check, but backtracked for some
    // other reason. In such a case, these lemmas are likely to be irrelevant
    // and possibly even harmful. If we produce proofs, their proofs have most
    // likely been deallocated already as well.
    d_im.clearPending();
    d_im.clearWaitingLemmas();
  }
  // check with the non-linear solver at last call
  if (level == Theory::EFFORT_LAST_CALL)
  {
    // If we computed lemmas in the last FULL_EFFORT check, send them now.
    if (d_im.hasPendingLemma())
    {
      d_im.doPendingFacts();
      d_im.doPendingLemmas();
      d_im.doPendingPhaseRequirements();
    }
    return;
  }
  // otherwise, check with the linear solver
  if (d_internal->postCheck(level))
  {
    // linear solver emitted a conflict or lemma, return
    return;
  }
  //simplexTime.stop();
  if (d_im.hasSent())
  {
    return;
  }

  if (Theory::fullEffort(level))
  {
    d_arithModelCache.clear();
    d_arithModelCacheIllTyped.clear();
    d_arithModelCacheSubs.clear();
    d_arithModelCacheSet = false;
    std::set<Node> termSet;
    if (d_nonlinearExtension != nullptr)
    {
      updateModelCache(termSet);
      // Check at full effort. This may either send lemmas or otherwise
      // buffer lemmas that we send at last call.
      d_nonlinearExtension->checkFullEffort(d_arithModelCache, termSet);
      // if we already sent a lemma, we are done
      if (d_im.hasSent())
      {
        return;
      }
    }
    else if (d_internal->foundNonlinear())
    {
      // set incomplete
      d_im.setModelUnsound(IncompleteId::ARITH_NL_DISABLED);
    }
    // If we won't be doing a last call effort check (which implies that
    // models will be computed), we must sanity check the integer model
    // from the linear solver now. We also must update the model cache
    // if we did not do so above.
    if (d_nonlinearExtension == nullptr)
    {
      updateModelCache(termSet);
    }
    sanityCheckIntegerModel();
    // Now, finalize the model cache, which constructs a substitution to be
    // used for getEqualityStatus.
    finalizeModelCache();
  }
}

bool TheoryArith::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  if (d_localSearchExtension != nullptr)
  {
    d_localSearchExtension->notifyFact(atom, pol, fact, isPrereg, isInternal);
    // UNDO THIS LATER!!!!
    //return true;
  }

  Trace("arith-check") << "TheoryArith::preNotifyFact: " << fact
                       << ", isPrereg=" << isPrereg
                       << ", isInternal=" << isInternal << std::endl;
  // We do not assert to the equality engine of arithmetic in the standard way,
  // hence we return "true" to indicate we are finished with this fact.
  bool ret = true;
  if (options().arith.arithEqSolver)
  {
    // the equality solver may indicate ret = false, after which the assertion
    // will be asserted to the equality engine in the default way.
    ret = d_eqSolver->preNotifyFact(atom, pol, fact, isPrereg, isInternal);
  }
  // we also always also notify the internal solver
  d_internal->preNotifyFact(atom, pol, fact);
  return ret;
}

bool TheoryArith::needsCheckLastEffort() {
  if (d_nonlinearExtension != nullptr)
  {
    return d_nonlinearExtension->hasNlTerms();
  }
  return false;
}

TrustNode TheoryArith::explain(TNode n)
{
  // if the equality solver has an explanation for it, use it
  TrustNode texp = d_eqSolver->explain(n);
  if (!texp.isNull())
  {
    return texp;
  }
  return d_internal->explain(n);
}

void TheoryArith::propagate(Effort e) {
  d_internal->propagate(e);
}


bool TheoryArith::collectModelInfo(TheoryModel* m,
                                   const std::set<Node>& termSet)
{
  // if the solution was found by local search return it
  if (d_localSearchExtension != nullptr)
  {
    if (d_localSearchExtension->foundASolution){
    std::cout << "CVC5::SolutionFoundByLS=1\n";
    return d_localSearchExtension->collectModelInfo(m, termSet);
    }
    //AlwaysAssert(false);
  }
  // If we have a buffered lemma (from the non-linear extension), then we
  // do not assert model values, since those values are likely incorrect.
  // Moreover, the model does not need to satisfy the assertions, so
  // arbitrary values can be used for arithmetic terms. Hence, we do
  // nothing here. The buffered lemmas will be sent immediately
  // at LAST_CALL effort (see postCheck).
  if (d_im.hasPendingLemma())
  {
    return true;
  }
  std::cout << "CVC5::SolutionFoundBySimplex=1\n";
  // this overrides behavior to not assert equality engine
  return collectModelValues(m, termSet);
}

bool TheoryArith::collectModelValues(TheoryModel* m,
                                     const std::set<Node>& termSet)
{
  if (TraceIsOn("arith::model"))
  {
    Trace("arith::model") << "arithmetic model after pruning" << std::endl;
    for (const auto& p : d_arithModelCache)
    {
      Trace("arith::model") << "\t" << p.first << " -> " << p.second << std::endl;
    }
  }

  updateModelCacheInternal(termSet);

  // We are now ready to assert the model.
  for (const std::pair<const Node, Node>& p : d_arithModelCache)
  {
    if (termSet.find(p.first) == termSet.end())
    {
      continue;
    }
    // do not assert non-leafs e.g. non-linear multiplication terms,
    // transcendental functions, etc.
    if (!Theory::isLeafOf(p.first, TheoryId::THEORY_ARITH))
    {
      continue;
    }
    // maps to constant of same type
    Assert(p.first.getType() == p.second.getType())
        << "Bad type : " << p.first << " -> " << p.second;
    if (m->assertEquality(p.first, p.second, true))
    {
      continue;
    }
    Assert(false) << "A model equality could not be asserted: " << p.first
                  << " == " << p.second << std::endl;
    // If we failed to assert an equality, it is likely due to theory
    // combination, namely the repaired model for non-linear changed
    // an equality status that was agreed upon by both (linear) arithmetic
    // and another theory. In this case, we must add a lemma, or otherwise
    // we would terminate with an invalid model. Thus, we add a splitting
    // lemma of the form ( x = v V x != v ) where v is the model value
    // assigned by the non-linear solver to x.
    if (d_nonlinearExtension != nullptr)
    {
      Node eq = p.first.eqNode(p.second);
      Node lem = NodeManager::currentNM()->mkNode(Kind::OR, eq, eq.negate());
      bool added = d_im.lemma(lem, InferenceId::ARITH_SPLIT_FOR_NL_MODEL);
      
      AlwaysAssert(added) << "The lemma was already in cache. Probably there is something wrong with theory combination...";
    }
    return false;
  }
  return true;
}

void TheoryArith::notifyRestart(){
  d_internal->notifyRestart();
}

void TheoryArith::presolve(){
  // if (d_localSearchExtension != nullptr)
  // {
  //   d_localSearchExtension->presolve();
  // }
  d_internal->presolve();
}

EqualityStatus TheoryArith::getEqualityStatus(TNode a, TNode b) {
  Trace("arith-eq-status") << "TheoryArith::getEqualityStatus(" << a << ", " << b << ")" << std::endl;
  if (a == b)
  {
    Trace("arith-eq-status") << "...return (trivial) true" << std::endl;
    return EQUALITY_TRUE_IN_MODEL;
  }
  if (d_arithModelCache.empty())
  {
    EqualityStatus es = d_internal->getEqualityStatus(a, b);
    Trace("arith-eq-status") << "...return (from linear) " << es << std::endl;
    return es;
  }
  Trace("arith-eq-status") << "Evaluate under " << d_arithModelCacheSubs.d_vars << " / "
                 << d_arithModelCacheSubs.d_subs << std::endl;
  Node diff = NodeManager::currentNM()->mkNode(Kind::SUB, a, b);
  // do not traverse non-linear multiplication here, since the value of
  // multiplication in this method should consider the value of the
  // non-linear multiplication term, and not its evaluation.
  std::optional<bool> isZero =
      isExpressionZero(d_env, diff, d_arithModelCacheSubs, false);
  if (isZero)
  {
    EqualityStatus es =
        *isZero ? EQUALITY_TRUE_IN_MODEL : EQUALITY_FALSE_IN_MODEL;
    Trace("arith-eq-status") << "...return (from evaluate) " << es << std::endl;
    return es;
  }
  Trace("arith-eq-status") << "...return unknown" << std::endl;
  return EQUALITY_UNKNOWN;
}

Node TheoryArith::getCandidateModelValue(TNode var)
{
  var = var.getKind() == Kind::TO_REAL ? var[0] : var;
  std::map<Node, Node>::iterator it = d_arithModelCache.find(var);
  if (it != d_arithModelCache.end())
  {
    return it->second;
  }
  return d_internal->getCandidateModelValue(var);
}

std::pair<bool, Node> TheoryArith::entailmentCheck(TNode lit)
{
  return d_internal->entailmentCheck(lit);
}

eq::ProofEqEngine* TheoryArith::getProofEqEngine()
{
  return d_im.getProofEqEngine();
}

void TheoryArith::updateModelCache(std::set<Node>& termSet)
{
  if (!d_arithModelCacheSet)
  {
    collectAssertedTermsForModel(termSet);
    updateModelCacheInternal(termSet);
  }
}
void TheoryArith::updateModelCacheInternal(const std::set<Node>& termSet)
{
  if (!d_arithModelCacheSet)
  {
    d_arithModelCacheSet = true;
    d_internal->collectModelValues(
        termSet, d_arithModelCache, d_arithModelCacheIllTyped);
  }
}

void TheoryArith::finalizeModelCache()
{
  // make into substitution
  for (const auto& [node, repl] : d_arithModelCache)
  {
    Assert(repl.getType().isRealOrInt());
    // we only keep the domain of the substitution that is for leafs of
    // arithmetic; otherwise we are using the value of the abstraction of
    // non-linear term from the linear solver, which can be incorrect.
    if (Theory::isLeafOf(node, TheoryId::THEORY_ARITH))
    {
      d_arithModelCacheSubs.add(node, repl);
    }
  }
}

bool TheoryArith::sanityCheckIntegerModel()
{
  // Double check that the model from the linear solver respects integer types,
  // if it does not, add a branch and bound lemma. This typically should never
  // be necessary, but is needed in rare cases.
  if (Configuration::isAssertionBuild())
  {
    for (CVC5_UNUSED const auto& p : d_arithModelCache)
    {
      Assert(p.first.getType() == p.second.getType())
          << "Bad type: " << p.first << " -> " << p.second;
    }
  }
  bool addedLemma = false;
  bool badAssignment = false;
  Trace("arith-check") << "model:" << std::endl;
  for (const auto& p : d_arithModelCacheIllTyped)
  {
    Trace("arith-check") << p.first << " -> " << p.second << std::endl;
    AlwaysAssert(p.first.getType().isInteger() && !p.second.getType().isInteger());
    warning() << "TheoryArithPrivate generated a bad model value for "
                 "integer variable "
              << p.first << " : " << p.second << std::endl;
    // must branch and bound
    std::vector<TrustNode> lems =
        d_bab.branchIntegerVariable(p.first, p.second.getConst<Rational>());
     Trace("arith-check") << "lems:" << lems.size() << std::endl;  
    for (const TrustNode& lem : lems)
    {
      if (d_im.trustedLemma(lem, InferenceId::ARITH_BB_LEMMA))
      {
        addedLemma = true;
      }
      Trace("arith-check") << "for some reason lemma was not sent\n";
    }
    badAssignment = true;
  }
  if (addedLemma)
  {
    // we had to add a branch and bound lemma since the linear solver assigned
    // a non-integer value to an integer variable.
    return true;
  }
  // this would imply that linear arithmetic's model failed to satisfy a branch
  // and bound lemma
  AlwaysAssert(!badAssignment)
      << "Bad assignment from TheoryArithPrivate::collectModelValues, and no "
         "branching lemma was sent";
  return false;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
