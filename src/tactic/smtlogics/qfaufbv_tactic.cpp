/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfaufbv_tactic.cpp

Abstract:

    Tactic for QF_AUFBV benchmarks.

Author:

    Leonardo (leonardo) 2012-02-23

Notes:

--*/
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "tactic/bv/max_bv_sharing_tactic.h"
#include "tactic/bv/bv_size_reduction_tactic.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "sat/tactic/sat_tactic.h"
#include "smt/tactic/smt_tactic.h"
#include "tactic/aig/aig_tactic.h"
#include "ackermannization/ackermannize_bv_tactic.h"
#include "sat/sat_solver/inc_sat_solver.h"
#include "tactic/bv/bvarray2uf_tactic.h"
#include <iostream>

#define MEMLIMIT 300


static tactic * main_pp(tactic* t) {
    params_ref p;
    p.set_bool("elim_and", true);
    p.set_bool("push_ite_bv", true);
    p.set_bool("blast_distinct", true);
    return using_params(t, p);
}

static tactic * mk_pp_qfbv_light_preamble(ast_manager& m, params_ref const& p) {

    params_ref solve_eq_p;
    // conservative guassian elimination.
    solve_eq_p.set_uint("solve_eqs_max_occs", 2);

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);
    simp2_p.set_bool("flat", true); // required by som
    simp2_p.set_bool("hoist_mul", false); // required by som

    return
            and_then(
                mk_simplify_tactic(m),
                mk_propagate_values_tactic(m),
                using_params(mk_solve_eqs_tactic(m), solve_eq_p),
                mk_elim_uncnstr_tactic(m),
                //mk_bv_size_reduction_tactic(m),  // get bv_size_reduction back
                //using_params(mk_solve_eqs_tactic(m), solve_eq_p),  // pinpoint: this can handle some "fast sat" cases
                using_params(mk_simplify_tactic(m), simp2_p),

                mk_bvarray2uf_tactic(m, p),        // reduce bv array to bv(with uninterpreted function)
                mk_ackermannize_bv_tactic(m, p),   // TODO: do ackermannization here or after max_bv_sharing?


                mk_max_bv_sharing_tactic(m)
                );
}


static tactic * mk_pp_qfbv_preamble(ast_manager& m, params_ref const& p) {

    params_ref solve_eq_p;
    // conservative guassian elimination.
    solve_eq_p.set_uint("solve_eqs_max_occs", 2);

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);
    simp2_p.set_bool("flat", true); // required by som
    simp2_p.set_bool("hoist_mul", false); // required by som

    params_ref hoist_p;
    hoist_p.set_bool("hoist_mul", true);
    hoist_p.set_bool("som", false);

    return
            and_then(
                mk_simplify_tactic(m),
                mk_propagate_values_tactic(m),
                using_params(mk_solve_eqs_tactic(m), solve_eq_p),
                mk_elim_uncnstr_tactic(m),
                if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
                //using_params(mk_solve_eqs_tactic(m), solve_eq_p),  // pinpoint: this can handle some "fast sat" cases

                using_params(mk_simplify_tactic(m), simp2_p),
                using_params(mk_simplify_tactic(m), hoist_p),

                mk_bvarray2uf_tactic(m, p),        // reduce bv array to bv(with uninterpreted function)
                mk_ackermannize_bv_tactic(m, p),   // TODO: do ackermannization here or after max_bv_sharing?

                mk_max_bv_sharing_tactic(m)
                );
}




tactic * mk_pp_qfbv_tactic(ast_manager& m, params_ref const & p, tactic* sat) {
    params_ref local_ctx_p = p;
    local_ctx_p.set_bool("local_ctx", true);

    params_ref solver_p;
    solver_p.set_bool("preprocess", false); // preprocessor of smt::context is not needed.

    params_ref no_flat_p;
    no_flat_p.set_bool("flat", false);

    params_ref ctx_simp_p;
    ctx_simp_p.set_uint("max_depth", 32);
    ctx_simp_p.set_uint("max_steps", 50000000);

    params_ref big_aig_p;
    big_aig_p.set_bool("aig_per_assertion", false);


    tactic* preamble_st = mk_pp_qfbv_preamble(m, p);
    tactic * st = main_pp(and_then(preamble_st,
                                            mk_bit_blaster_tactic(m),
                                                     when(mk_lt(mk_memory_probe(), mk_const_probe(MEMLIMIT)),
                                                          and_then(using_params(and_then(mk_simplify_tactic(m),
                                                                                         mk_solve_eqs_tactic(m)),
                                                                                local_ctx_p),
                                                                                     using_params(mk_aig_tactic(),
                                                                                                  big_aig_p))),
                                                     sat));
    st->updt_params(p);
    return st;

}

tactic * mk_pp_qfbv_light_tactic(ast_manager& m, params_ref const & p, tactic* sat) {
    tactic* preamble_st = mk_pp_qfbv_light_preamble(m, p);
    tactic * st = main_pp(and_then(preamble_st,mk_bit_blaster_tactic(m),sat));
    st->updt_params(p);
    return st;
}

tactic * mk_pp_qfbv_light_tactic(ast_manager & m, params_ref const & p) {
    // std::cout << "Using AUFBV tactic..\n";
    tactic * new_sat = cond(mk_produce_proofs_probe(),
                            and_then(mk_simplify_tactic(m), mk_smt_tactic(m)),
                            mk_psat_tactic(m, p));

    return mk_pp_qfbv_light_tactic(m, p, new_sat);
}


tactic * mk_pp_qfbv_tactic(ast_manager & m, params_ref const & p) {

    tactic * new_sat = cond(mk_produce_proofs_probe(),
                            and_then(mk_simplify_tactic(m), mk_smt_tactic(m)),
                            mk_psat_tactic(m, p));
    return mk_pp_qfbv_tactic(m, p, new_sat);
}


///////////////////////////// Interface /////////////////////////////////

# if 0
// replace using our tactic...
tactic * mk_qfaufbv_tactic(ast_manager & m, params_ref const & p) {
    // std::cout << "Using AUFBV tactic..\n";
    tactic * new_sat = cond(mk_produce_proofs_probe(),
                            and_then(mk_simplify_tactic(m), mk_smt_tactic(m)),
                            mk_psat_tactic(m, p));

    return mk_pp_qfbv_light_tactic(m, p, new_sat);
    // return mk_pp_qfbv_tactic(m, p, new_sat);
}
#else

tactic * mk_qfaufbv_tactic(ast_manager & m, params_ref const & p) {
    // std::cout << "Using AUFBV tactic..\n";
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("sort_store", true);

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    params_ref ctx_simp_p;
    ctx_simp_p.set_uint("max_depth", 32);
    ctx_simp_p.set_uint("max_steps", 5000000);

    params_ref solver_p;
    solver_p.set_bool("array.simplify", false); // disable array simplifications at old_simplify module

    tactic * preamble_st = and_then(mk_simplify_tactic(m),
                                    mk_propagate_values_tactic(m),
                                    // using_params(mk_ctx_simplify_tactic(m), ctx_simp_p),
                                    mk_solve_eqs_tactic(m),
                                    mk_elim_uncnstr_tactic(m),
                                    if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
                                    using_params(mk_simplify_tactic(m), simp2_p),
                                    mk_max_bv_sharing_tactic(m)
                                    );

    tactic * st = using_params(and_then(preamble_st,
                                        using_params(mk_smt_tactic(m), solver_p)),
                               main_p);
    
    st->updt_params(p);
    return st;
}

#endif
