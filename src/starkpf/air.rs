use atomic_refcell::AtomicRefCell;
use super::{
    BaseElement, FieldElement, ProofOptions, TRACE_WIDTH, N, HASH_RATE_WIDTH, HASH_CYCLE_LEN, 
    HASH_STATE_WIDTH, HASH_DIGEST_WIDTH, TAU, BETA, PADDED_TRACE_LENGTH, M, SBALLEND, 
    aux_trace_table::{GAMMA, CAUX, ZAUX, WAUX, QWAUX, POLYMULTASSERT}, 
    PIT_START, PIT_END, PUBT, PUBA, QWIND, CTILDEASSERT, COM_START, COM_END, HTR, K, PIT_LEN};

use crate::{
    utils::{EvaluationResult, is_binary, poseidon_23_spec, are_equal}, 
    starkpf::{CIND, CTILDEIND, HASHIND, ZIND, ZRANGE, ZRANGEIND, QRANGE, RRANGE,
    QRANGEIND, QIND, RRANGEIND, RIND, QASSERT, RASSERT, SWAPASSERT, NEGASSERT, 
    ZASSERT, SWAPDECIND, SWAPDECASSERT, QRASSERT, AUX_WIDTH, WIND, SIGNIND, 
    ZLIMIT, WLOWIND, WLOWRANGE, WBIND, WHIGHIND, GAMMA2, WDECASSERT, WLOWLIMIT, 
    WLOWASSERT, WLOWRANGEIND, WHIGHSHIFT, WHIGHASSERT, WHIGHRANGEIND, WHIGHRANGE}};

use winterfell::{
    Air, AirContext, Assertion, ByteWriter, EvaluationFrame, Serializable, TraceInfo,
    TransitionConstraintDegree, SliceReader
};

// Dilithium AIR
// ================================================================================================

const HASH_CYCLE_MASK: [BaseElement; HASH_CYCLE_LEN] = [
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ZERO,
];

pub struct PublicInputs {
    // pub ctilde: [BaseElement; HASH_DIGEST_WIDTH],
    // pub z: [BaseElement; N*4],
    pub m: [BaseElement; HASH_DIGEST_WIDTH]
}

impl Serializable for PublicInputs {
    fn write_into<W: ByteWriter>(&self, _target: &mut W) {
        // target.write(&self.ctilde[..]);
    }
}
pub struct ThinDilAir {
    context: AirContext<BaseElement>,
    cache: AtomicRefCell<Vec<u8>>,
    // ctilde: [BaseElement; HASH_DIGEST_WIDTH],
    // z: [BaseElement; N*4],
    m: [BaseElement; HASH_DIGEST_WIDTH]
}

impl Air for ThinDilAir {
    type BaseField = BaseElement;
    type PublicInputs = PublicInputs;

    // CONSTRUCTOR
    // --------------------------------------------------------------------------------------------
    fn new(trace_info: TraceInfo, pub_inputs: Self::PublicInputs, options: ProofOptions) -> Self {
        // Same result spaces get reused when doing hashing_to_ball
        let mut main_degrees = Vec::new();

        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); N-TAU-1]); // c
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(3, vec![PADDED_TRACE_LENGTH]); TAU+1]); // c

        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); HASH_CYCLE_LEN]); //Q, Z, ZRANGEIND
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); HASH_CYCLE_LEN]); //R, ZRANGEIND
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); HASH_CYCLE_LEN]); //SIGN, ZRANGEIND

        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); 2*QRANGE]); // q_rangeproof, ZRANGEIND
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); 2*RRANGE]); // r_rangeproof, ZRANGEIND

        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); N]); 
        // swap_dec, ZRANGEIND, WLOWRANGEIND, WHIGHRANGEIND, WASSERT, ZASSERT, WIND, ZIND, QWIND

        main_degrees.append(&mut vec![TransitionConstraintDegree::new(1); HASH_DIGEST_WIDTH]); // ctilde
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(3, vec![PADDED_TRACE_LENGTH]); 6*HASH_STATE_WIDTH]); //hash_space

        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); 2]); //QASSERT (Assertion for rangeproof)
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); 2]); //RASSERT (Assertion for rangeproof)

        main_degrees.push(TransitionConstraintDegree::with_cycles(3, vec![PADDED_TRACE_LENGTH])); //SWAPASSERT
        main_degrees.push(TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH])); //NEGASSERT
        
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]);2]); //SWAPDECASSERT

        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); HASH_CYCLE_LEN]); //QRASSERT (Assertion for q.base + r = x)        
        
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); 2*4]); //WDECASSERT (Assertion for w1.w2=0 and w0.w2=0)
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); 4]); //WLOWASSERT (Assertion for w1 rangeproof)
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); 8]); //WHIGHASSERT (Assertion for w0 rangeproof)
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); HASH_DIGEST_WIDTH]); //CTILDEASSERT (Assertion for ctilde=h(mu||w1))

        debug_assert_eq!(TRACE_WIDTH+AUX_WIDTH, trace_info.width());

        let mut aux_degrees = Vec::new();
        aux_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); AUX_WIDTH-1]);
        aux_degrees.push(TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]));
        aux_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); 4]);

        ThinDilAir {
            context: AirContext::new_multi_segment(
                trace_info, 
                main_degrees,
                aux_degrees,
                316,
                14, 
                options
            ).set_num_transition_exemptions(2),
            m: pub_inputs.m,
            cache: AtomicRefCell::new(vec![]),
        }
    }

    fn context(&self) -> &AirContext<Self::BaseField> {
        &self.context
    }

    fn evaluate_transition<E: FieldElement + From<Self::BaseField>>(
        &self,
        frame: &EvaluationFrame<E>,
        periodic_values: &[E],
        result: &mut [E],
    ) {
        let current = frame.current();
        let next = frame.next();
        
        debug_assert_eq!(TRACE_WIDTH, current.len());
        debug_assert_eq!(TRACE_WIDTH, next.len());

        let qr_flag = periodic_values[0];
        let notqr_flag = periodic_values[1];
        let qrdec_flag = periodic_values[2];
        
        let ccopy_flag = periodic_values[4];
        let hashmask_flag = periodic_values[5];
        let cinserthashmask_flag = periodic_values[6];
        let winserthashmask_flag = periodic_values[7];
        
        let ctilde_flag = periodic_values[9];
        let matmul_flag = periodic_values[10];
        
        let r_mod = periodic_values[11];
        let q_mod = periodic_values[12];

        let s = &periodic_values[13..(13+N)];
        let qr_base = periodic_values[13+N];
        let ark = &periodic_values[(14+N)..];

        let powers_of_2 = vec![
            E::ONE,
            E::from(2u32),
            E::from(4u32),
            E::from(8u32),
            E::from(16u32),
            E::from(32u32),
            E::from(64u32),
            E::from(128u32),
            E::from(256u32),
            E::from(512u32),
            E::from(1024u32),
            E::from(2048u32),
            E::from(4096u32),
            E::from(8192u32),
            E::from(16384u32),
            E::from(32768u32),
            E::from(65536u32),
            E::from(131072u32),
            E::from(262144u32),
            E::from(524288u32),
            E::from(1048576u32),
        ];

        // Assert the poseidon round was computed correctly was computed correctly whenever a permutation needs to be applied
        assert_hash(&mut result[HASHIND..(HASHIND+6*HASH_STATE_WIDTH)],
            &current[HASHIND..(HASHIND+3*HASH_STATE_WIDTH)],
            &next[HASHIND..(HASHIND+3*HASH_STATE_WIDTH)],
            &ark,
            hashmask_flag
        );

        // Copy claimed WHIGH into hash_space at beginning of every cycle or ensure hash rate space is copied correctly
        for i in 0..HASH_RATE_WIDTH {
            result.agg_constraint(HASHIND+i, winserthashmask_flag, next[HASHIND+i] - current[HASHIND+i] - next[WHIGHIND+i]);
            result.agg_constraint(HASHIND+i, cinserthashmask_flag, next[HASHIND+i] - current[HASHIND+i]);
        }

        // Assert that the hash_capacity was copied correctly at the end of each round
        assert_hash_copy(&mut result[HASHIND..(HASHIND+6*HASH_STATE_WIDTH)],
            &current[HASHIND..(HASHIND+3*HASH_STATE_WIDTH)],
            &next[HASHIND..(HASHIND+3*HASH_STATE_WIDTH)],
            &ark[0..3*HASH_STATE_WIDTH],
            cinserthashmask_flag+winserthashmask_flag
        );

        //////////////////////////////////////////////////////////////////////////////////////////////////

        // Assert rotation of WHIGH by 4 to the left
        result.agg_constraint(WHIGHIND+HASH_RATE_WIDTH-1, matmul_flag, next[WHIGHIND+HASH_RATE_WIDTH-1] - current[WHIGHIND+3]);
        result.agg_constraint(WHIGHIND+HASH_RATE_WIDTH-2, matmul_flag, next[WHIGHIND+HASH_RATE_WIDTH-2] - current[WHIGHIND+2]);
        result.agg_constraint(WHIGHIND+HASH_RATE_WIDTH-3, matmul_flag, next[WHIGHIND+HASH_RATE_WIDTH-3] - current[WHIGHIND+1]);
        result.agg_constraint(WHIGHIND+HASH_RATE_WIDTH-4, matmul_flag, next[WHIGHIND+HASH_RATE_WIDTH-4] - current[WHIGHIND]);
        for i in 0..(HASH_RATE_WIDTH-4) {
            result.agg_constraint(WHIGHIND+i, matmul_flag, next[WHIGHIND+i] - current[WHIGHIND+i+4]);
        }

        // Assert decomposition of W
        let twof = E::from(2u32);
        let gamma2 = E::from(GAMMA2);
        
        for i in 0..4 {
            result.agg_constraint(
                WIND+i, 
                matmul_flag, 
                current[WIND+i] - current[WLOWIND+i]-current[WHIGHIND+i]*twof*gamma2+current[WBIND]*gamma2
            );
            result.agg_constraint(WBIND+i, matmul_flag, is_binary(current[WBIND+i])); //w2.(1-w2)=0
            result.agg_constraint(WDECASSERT+2*i, matmul_flag, current[WHIGHIND+i]*current[WBIND+i]); //w1.w2=0
            result.agg_constraint(WDECASSERT+2*i+1, matmul_flag, current[WLOWIND+i]*current[WBIND+i]); //w0.w2=0
        }

        let wlowlimitf = E::from(WLOWLIMIT);
        let (head, tail) = result.split_at_mut(WLOWASSERT);
        for i in 0..4{
            let value = current[WLOWIND + i] + wlowlimitf;
            
            assert_bitdec(
                &mut head[WLOWRANGEIND+i*WLOWRANGE..WLOWRANGEIND+(i+1)*WLOWRANGE], 
                &current[WLOWRANGEIND+i*WLOWRANGE..WLOWRANGEIND+(i+1)*WLOWRANGE], 
                value, 
                matmul_flag,
                &mut tail[i],
                &powers_of_2
            );
        }

        let whighshiftf = E::from(WHIGHSHIFT);
        let (head, tail) = result.split_at_mut(WHIGHASSERT);
        for i in 0..8{
            let mut value = current[WHIGHIND + i/2];
            if i%2 == 1 {
                value += whighshiftf;
            }
            
            assert_bitdec(
                &mut head[WHIGHRANGEIND+i*WHIGHRANGE..WHIGHRANGEIND+(i+1)*WHIGHRANGE], 
                &current[WHIGHRANGEIND+i*WHIGHRANGE..WHIGHRANGEIND+(i+1)*WHIGHRANGE], 
                value, 
                matmul_flag,
                &mut tail[i],
                &powers_of_2
            );
        }

        // Z BIT DECOMPOSITION
        let zlimitf = E::from(ZLIMIT);
        let betaf = E::from(BETA);
        
        let (head, tail) = result.split_at_mut(ZASSERT);
        for i in 0..8{
            let mut value = current[ZIND + i/2] + zlimitf;
            if i%2 == 1 {
                value += betaf;
            }
            
            assert_bitdec(
                &mut head[ZRANGEIND+i*ZRANGE..ZRANGEIND+(i+1)*ZRANGE], 
                &current[ZRANGEIND+i*ZRANGE..ZRANGEIND+(i+1)*ZRANGE], 
                value, 
                matmul_flag,
                &mut tail[i],
                &powers_of_2
            );
        }
 
        // Q BIT DECOMPOSITION
        let (head, tail) = result.split_at_mut(QASSERT);
        for i in 0..2 {
            let mut value = current[QIND];
            if i%2 == 1 {
                value += q_mod;
            }
            assert_bitdec(
                &mut head[QRANGEIND+i*QRANGE..QRANGEIND+(i+1)*QRANGE], 
                &current[QRANGEIND+i*QRANGE..QRANGEIND+(i+1)*QRANGE], 
                value, 
                qrdec_flag,
                &mut tail[i],
                &powers_of_2
            );
        }
        
        // Assert rotation of Q by 1 to the left
        result.agg_constraint(QIND+HASH_CYCLE_LEN-1, qr_flag, next[QIND+HASH_CYCLE_LEN-1] - current[QIND]);
        for i in 0..(HASH_CYCLE_LEN-1) {
            result.agg_constraint(QIND+i, qr_flag, next[QIND+i] - current[QIND+i+1]);
        }
        
        //  R BIT DECOMPOSITION
        let (head, tail) = result.split_at_mut(RASSERT);
        for i in 0..2 {
            let mut value = current[RIND];
            if i%2 == 1 {
                value += r_mod;
            }
            assert_bitdec(
                &mut head[RRANGEIND+i*RRANGE..RRANGEIND+(i+1)*RRANGE],
                &current[RRANGEIND+i*RRANGE..RRANGEIND+(i+1)*RRANGE], 
                value, 
                qrdec_flag,
                &mut tail[i],
                &powers_of_2
            );
        }

        // Assert rotation of R by 1 to the left
        result.agg_constraint(RIND+HASH_CYCLE_LEN-1, qr_flag, next[RIND+HASH_CYCLE_LEN-1] - current[RIND]);
        for i in 0..(HASH_CYCLE_LEN-1) {
            result.agg_constraint(RIND+i, qr_flag, next[RIND+i] - current[RIND+i+1]);
        }
        
        // Assert q.base + r = x
        for i in 0..HASH_CYCLE_LEN{
            result[QRASSERT+i] = (notqr_flag)*(next[HASHIND+i] - next[RIND+i] - (qr_base+E::from(i as u32))*next[QIND+i]);
        }
        
        // Swap, Negate and Copy c
        let (mut lhs, mut rhs) = (E::ZERO, E::ZERO);
        
        for i in 0..N{
            lhs+= E::from(i as u32)*current[SWAPDECIND+i];
            result.agg_constraint(SWAPDECIND+i, qrdec_flag, is_binary(current[SWAPDECIND+i]));
        }

        result.agg_constraint(SWAPDECASSERT, qrdec_flag, lhs - current[RIND]);

        lhs = E::ZERO;
        for i in 0..N{
            lhs+= current[SWAPDECIND+i];
        }
        result.agg_constraint(SWAPDECASSERT+1, qrdec_flag, lhs - E::ONE);

        lhs = E::ZERO;
        let mut s_location = E::ZERO;
        for i in 0..N{
            s_location += E::from(i as u32)*s[i];
            lhs += next[SWAPDECIND+i]*current[CIND+i];
            rhs += s[i]*next[CIND+i];
        }
        result.agg_constraint(SWAPASSERT, qrdec_flag, (next[RIND] - s_location)*(lhs-rhs));

        lhs = E::ZERO;
        // rhs = E::ZERO;

        for i in 0..N{
            lhs += next[SWAPDECIND+i]*next[CIND+i];
        }

        rhs = E::ONE - E::from(2 as u64)*next[SIGNIND];
        
        result.agg_constraint(NEGASSERT, qrdec_flag, lhs-rhs);
        
        // Assert copy of c but ignore two positions defined by t and s when qrdec_flag = 1.
        for i in 0..N {
            result.agg_constraint(
                CIND+i, 
                qrdec_flag, 
                (E::ONE - next[SWAPDECIND+i])*(E::ONE - s[i])*(next[CIND+i] - current[CIND+i])
            );
        }

        // Assert copy of C when ccopy_flag = 1
        for i in 0..N{
            result.agg_constraint(CIND+i, ccopy_flag, next[CIND+i] - current[CIND+i]);
        }

        // Assert rotation of C by 1 to the left when matmul_flag = 1
        result.agg_constraint(CIND+N-1, matmul_flag, next[CIND+N-1] - current[CIND]);
        for i in 0..(N-1) {
            result.agg_constraint(CIND+i, matmul_flag, next[CIND+i] - current[CIND+i+1]);
        }
        
        // Copy ctilde
        for i in 0..HASH_DIGEST_WIDTH {
            result[CTILDEIND+i] += next[CTILDEIND+i] - current[CTILDEIND+i];
        }


        // Assert that ctilde is equal to h(mu||w) -- hashstate at step PIT_END-1
        for i in 0..HASH_DIGEST_WIDTH {
            result.agg_constraint(
                CTILDEASSERT + i, 
                ctilde_flag.into(), 
                are_equal(current[CTILDEIND+i],current[HASHIND+i])
            );
        }
    }

    fn evaluate_aux_transition<F, E>(
            &self,
            main_frame: &EvaluationFrame<F>,
            aux_frame: &EvaluationFrame<E>,
            periodic_values: &[F],
            aux_rand_elements: &winterfell::AuxTraceRandElements<E>,
            result: &mut [E],
        ) where
            F: FieldElement<BaseField = Self::BaseField>,
            E: FieldElement<BaseField = Self::BaseField> + winterfell::math::ExtensionOf<F>, {
                let polycopy_flag = periodic_values[3];
                let polymult_flag = periodic_values[8];
                let matmul_flag = periodic_values[10];

                
                let main_current = main_frame.current();
                let _main_next = main_frame.next();

                let aux_current = aux_frame.current();
                let aux_next = aux_frame.next();

                let random_elements = aux_rand_elements.get_segment_elements(0);

                // Carrying out the following PIT
                // Q(GAMMA).(GAMMA^256 + 1) + W(GAMMA) = A(GAMMA).z(GAMMA) - t(GAMMA).c(GAMMA)
                // Q, W, z, t are 4x1 vectors of degree 255 polynomials
                // A is a 4x4 matric of degree 255 polynomials
                // c is a degree 255 polynomial
                
                // Evaluate T and A at point random_elements[0]
                // We need a hacky solution with caching because of restrictions in winterfell and rust
                let mut t_eval = [E::ZERO; 4];
                let mut a_eval = [[E::ZERO; 4]; 4];

                let mut cache = self.cache.borrow_mut();
                if cache.len() > 0 {
                    let mut reader = SliceReader::new(&cache);
                    for j in 0..4 {
                    if let Ok(v) = E::read_from(&mut reader) {
                        t_eval[j] = v;
                    } else {
                        panic!("recover from cache failed");
                    }
                }

                    for j in 0..4 {
                        for i in 0..4 {
                            if let Ok(v) = E::read_from(&mut reader) {
                                a_eval[i][j] = v;
                            } else {
                                panic!("recover from cache failed");
                            }
                        }
                    }
                } else {
                    let mut pubt: [[E; N]; 4] = [[E::ZERO; N]; 4];
                    for j in 0..4 {
                        pubt[j] = PUBT[j].map(E::from);
                        t_eval[j] = poly_eval(&pubt[j], random_elements[0]);
                        t_eval[j].write_into(&mut *cache);
                    }
                    let mut puba: [[[E; N]; 4]; 4] = [[[E::ZERO; N]; 4]; 4];
                    for j in 0..4 {
                        for i in 0..4 {
                            puba[i][j] = PUBA[i][j].map(E::from);
                            a_eval[i][j] = poly_eval(&puba[i][j], random_elements[0]);
                            a_eval[i][j].write_into(&mut *cache);
                        }
                    }
                }

                let c_eval = aux_current[CAUX];
                let w_eval = &aux_current[WAUX..WAUX+4];
                let qw_eval = &aux_current[QWAUX..QWAUX+4];
                let z_eval = &aux_current[ZAUX..ZAUX+4];

                let mut lhs:E;
                let mut rhs:E;
                for ii in 0..4{
                    lhs = qw_eval[ii]*(random_elements[0].exp(E::PositiveInteger::from(256 as u32)) + E::ONE) + w_eval[ii];
                    rhs = E::ZERO;
                    
                    for i in 0..4{
                        rhs += a_eval[ii][i]*z_eval[i]; 
                    }

                    rhs -= c_eval*t_eval[ii];

                    result.agg_constraint(
                        POLYMULTASSERT + ii, 
                        polymult_flag.into(), 
                        are_equal(lhs,rhs)
                    );
                }
                
                // evaluation aggregation check
                // todo: can move this to mod.rs constants and save some work
                let mut ec_tuples: Vec<(usize,usize)> = Vec::new();
                ec_tuples.push((CAUX, CIND));
                for i in 0..4 {
                    ec_tuples.push((ZAUX+i, ZIND+i));
                    ec_tuples.push((WAUX+i, WIND+i));
                    ec_tuples.push((QWAUX+i, QWIND+i));
                }

                result.agg_constraint(
                    GAMMA, 
                    matmul_flag.into(), 
                    are_equal(aux_next[GAMMA],aux_current[GAMMA]*random_elements[0],)
                );
                result.agg_constraint(
                    GAMMA, 
                    polycopy_flag.into(), 
                    are_equal(aux_next[GAMMA],aux_current[GAMMA],)
                );

                ec_tuples.iter().for_each(
                    |ec| 
                    poly_eval_assert(
                        ec.0,
                        matmul_flag.into(),
                        polycopy_flag.into(),
                        ec.1,
                        result,
                        &aux_next,
                        &aux_current,
                        main_current
                    )
                );
    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        let mut main_assertions = Vec::new();
        // Assert HASH_STATE is zero in all registers except the first HASH_DIGEST_WIDTH+1
        for i in HASH_DIGEST_WIDTH+1..HASH_STATE_WIDTH{
            main_assertions.push(Assertion::single(HASHIND+i, 0, BaseElement::ZERO));
        } 
        
        // Assert HASH_STATE is zero in all registers except the first HASH_RATE_WIDTH
        for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH{
            main_assertions.push(Assertion::single(HASHIND+i, COM_END, BaseElement::ZERO));
        }

        // Assert HASH_RATE..HASH_STATE is HTR on step COM_START
        for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH{
            main_assertions.push(Assertion::single(HASHIND+i, COM_START, BaseElement::from(HTR[i])));
        }

        // Assert 0..HASH_DIGEST is HTR+m on step COM_START
        for i in 0..HASH_DIGEST_WIDTH{
            main_assertions.push(Assertion::single(HASHIND+i, COM_START, BaseElement::from(HTR[i])+self.m[i]));
        }

        // Assert CIND in initialized to zero at the beginning (HASH_CYCLE_LEN-1)
        for i in 0..N{
            main_assertions.push(Assertion::single(CIND+i, HASH_CYCLE_LEN-1, BaseElement::ZERO));
        }

        // Assert highest coefficienct of qw is 0
        for i in 0..K{
            main_assertions.push(Assertion::single(QWIND+i, PIT_START-1 + PIT_LEN-4, BaseElement::ZERO));
        }
        main_assertions
    }

    fn get_aux_assertions<E: FieldElement<BaseField = Self::BaseField>>(
            &self,
            aux_rand_elements: &winterfell::AuxTraceRandElements<E>,
        ) -> Vec<Assertion<E>> {
        
        let mut aux_assertions = Vec::new();
        
        let random_elements = aux_rand_elements.get_segment_elements(0);
        
        aux_assertions.push(Assertion::single(GAMMA, PIT_START+1, random_elements[0]));
        
        aux_assertions.push(Assertion::single(CAUX, PIT_START, E::ZERO));
        for i in 0..K {
            aux_assertions.push(Assertion::single(ZAUX+i, PIT_START, E::ZERO));
            aux_assertions.push(Assertion::single(WAUX+i, PIT_START, E::ZERO));
            aux_assertions.push(Assertion::single(QWAUX+i, PIT_START, E::ZERO));
        }
        
        aux_assertions
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<Self::BaseField>> {
        let mut result = Vec::new();
        result.push(get_qr_mask());
        result.push(get_notqr_mask());
        result.push(get_qrdec_mask());
        result.push(get_polycopy_mask());
        result.push(get_ccopy_mask());
        result.push(get_hashmask_constants());
        result.push(get_copyhashmask_constants());
        result.push(get_inserthashmask_constants());
        result.push(get_polymult_mask());
        result.push(get_ctilde_flag());
        result.push(get_matmul_mask());
        result.push(get_r_mod());
        result.push(get_q_mod());
        result.append(&mut get_swap_constants());
        result.append(&mut poseidon_23_spec::get_round_constants());

        result
    }
}

fn assert_hash<E: FieldElement + From<BaseElement>>(
    result: &mut [E],
    current: &[E],
    next: &[E],
    ark: &[E],
    flag: E
) {
    poseidon_23_spec::enforce_round(
        &mut result[0..(2*HASH_STATE_WIDTH)],
        &current[0..(HASH_STATE_WIDTH)],
        &next[(2*HASH_STATE_WIDTH)..(3*HASH_STATE_WIDTH)],
        &ark[0..HASH_STATE_WIDTH],
        flag,
    );
    poseidon_23_spec::enforce_round(
        &mut result[(4*HASH_STATE_WIDTH)..(6*HASH_STATE_WIDTH)],
        &next[(2*HASH_STATE_WIDTH)..(3*HASH_STATE_WIDTH)],
        &next[(HASH_STATE_WIDTH)..(2*HASH_STATE_WIDTH)],
        &ark[HASH_STATE_WIDTH..2*HASH_STATE_WIDTH],
        flag,
    );
    poseidon_23_spec::enforce_round(
        &mut result[(2*HASH_STATE_WIDTH)..(4*HASH_STATE_WIDTH)],
        &next[(HASH_STATE_WIDTH)..(2*HASH_STATE_WIDTH)],
        &next[0..(HASH_STATE_WIDTH)],
        &ark[2*HASH_STATE_WIDTH..3*HASH_STATE_WIDTH],
        flag,
    );
}

fn poly_eval<E:FieldElement + From<BaseElement>>(
    coeffs: &[E],
    x: E,
) -> E {
    let mut eval = E::ZERO;
    let mut gamma_acc = E::ONE;
    for i in 0..N{
        eval += coeffs[i]*gamma_acc;
        gamma_acc = gamma_acc*x;
    }

    eval
}

fn poly_eval_assert<F: FieldElement, E:FieldElement + From<F>>(
    eval_index: usize,
    flag1: E,
    flag2: E,
    coeff_index: usize,
    result: &mut [E],
    aux_next: &[E],
    aux_current: &[E],
    main_current: &[F]
) {
    result.agg_constraint(
        eval_index, 
        flag1, 
        are_equal(aux_next[eval_index],aux_current[eval_index] + aux_current[GAMMA]*main_current[coeff_index].into(),)
    );

    result.agg_constraint(
        eval_index, 
        flag2, 
        are_equal(aux_next[eval_index],aux_current[eval_index],)
    ); 
}

fn assert_hash_copy<E: FieldElement + From<BaseElement>>(
    result: &mut [E],
    current: &[E],
    next: &[E],
    _ark: &[E],
    flag: E
) {
    // Asserting copy of HASH_CAPACITY
    for i in 0..3{
        for j in HASH_RATE_WIDTH..HASH_STATE_WIDTH{
            result[HASH_STATE_WIDTH*i + j] += flag*(current[HASH_STATE_WIDTH*i + j] - next[HASH_STATE_WIDTH*i + j]);
        }
    }
}

fn assert_bitdec<E: FieldElement + From<BaseElement>>(
    result: &mut[E], 
    bits: &[E],
    value: E, 
    flag: E,
    final_check: &mut E,
    powers_of_2: &[E]
) {
    let mut should_be_value = E::ZERO;
    for i in 0..bits.len() {
        result[i] += flag*is_binary(bits[i]);
        should_be_value += bits[i]*powers_of_2[i];
    }

    *final_check+=flag*(value - should_be_value);
}

fn get_matmul_mask() -> Vec<BaseElement> {
    let mut matmul_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];
    for i in PIT_START..PIT_END-4{
        if i%HASH_CYCLE_LEN < HASH_CYCLE_LEN-2 {
            matmul_mask[i] = BaseElement::ONE;
        }
    }

    matmul_mask
}

fn get_polycopy_mask() -> Vec<BaseElement> {
    let mut polycopy_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];
    for i in PIT_START..PIT_END{
        if i%HASH_CYCLE_LEN >= HASH_CYCLE_LEN-2 {
            polycopy_mask[i] = BaseElement::ONE;
        }
    }

    polycopy_mask
}

fn get_polymult_mask() -> Vec<BaseElement> {
    // Flag to check A(gamma).z(gamma) - c(gamma).t(gamma) = w(gamma) + (gamma^256 + 1).q(gamma)
    let mut polymult_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];
    polymult_mask[PIT_END-4] = BaseElement::ONE;

    polymult_mask
}

fn get_ctilde_flag() -> Vec<BaseElement> {
    // Flag to check A(gamma).z(gamma) - c(gamma).t(gamma) = w(gamma) + (gamma^256 + 1).q(gamma)
    let mut ctilde_flag = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];
    ctilde_flag[PIT_END-1] = BaseElement::ONE;

    ctilde_flag
}

fn get_ccopy_mask() -> Vec<BaseElement> {
    let mut ccopy_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    for i in (HASH_CYCLE_LEN)*(SBALLEND)..PIT_START{
        ccopy_mask[i] = BaseElement::ONE;
    }

    ccopy_mask
}

fn get_qr_mask() -> Vec<BaseElement> {
    let mut qr_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    for i in HASH_CYCLE_LEN-1..(HASH_CYCLE_LEN)*(SBALLEND){
        qr_mask[i] = HASH_CYCLE_MASK[i%HASH_CYCLE_LEN];
    }

    qr_mask
}

fn get_notqr_mask() -> Vec<BaseElement> {
    let mut notqr_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    // Check that (HASH_CYCLE_LEN)*(SBALLEND)-1 is correct
    for i in HASH_CYCLE_LEN-1..(HASH_CYCLE_LEN)*(SBALLEND)-1{
        notqr_mask[i] = BaseElement::ONE - HASH_CYCLE_MASK[i%HASH_CYCLE_LEN];
    }

    notqr_mask
}

fn get_qrdec_mask() -> Vec<BaseElement> {
    let mut qrdec_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    for i in HASH_CYCLE_LEN..(HASH_CYCLE_LEN)*(SBALLEND)-1 {
        qrdec_mask[i] = BaseElement::ONE;
    }

    qrdec_mask
}

fn get_r_mod() -> Vec<BaseElement> {
    let mut r_mod = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    for i in 0..TAU+1{
        // println!("r_mod: {}", 256 - (N-1-TAU+i) as u32);
        r_mod[HASH_CYCLE_LEN+i] = BaseElement::new(256 - (N-TAU+i) as u32);
    }

    r_mod
}

fn get_q_mod() -> Vec<BaseElement> {
    let mut q_mod = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    for i in 0..TAU+1{
        // println!("q_mod: {}", M/(N-1-TAU+i) as u32);
        q_mod[HASH_CYCLE_LEN+i] = BaseElement::new(M/(N-TAU+i) as u32);
    }

    q_mod
}

fn get_swap_constants() -> Vec<Vec<BaseElement>> {
    let mut swap_const = Vec::new();
    for _ in 0..N+1 {
        swap_const.push(vec![BaseElement::ZERO; PADDED_TRACE_LENGTH]);
    }
    for i in HASH_CYCLE_LEN-1..(SBALLEND)*HASH_CYCLE_LEN{
        swap_const[N-TAU+i-HASH_CYCLE_LEN][i] = BaseElement::ONE;
        swap_const[N][i] = BaseElement::new((N-TAU+i-HASH_CYCLE_LEN+1) as u32);
    }

    swap_const
}

fn get_hashmask_constants() -> Vec<BaseElement> {
    let mut hashmask_const = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];
    for i in 0..(HASH_CYCLE_LEN)*(SBALLEND){
        hashmask_const[i] = HASH_CYCLE_MASK[i%HASH_CYCLE_LEN];
    }

    for i in PIT_START..PIT_END{
        hashmask_const[i] = HASH_CYCLE_MASK[i%HASH_CYCLE_LEN];
    }

    hashmask_const
}

fn get_inserthashmask_constants() -> Vec<BaseElement> {
    let mut inserthashmask_const = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];
    for i in PIT_START..PIT_END-1{
        inserthashmask_const[i] = BaseElement::ONE - HASH_CYCLE_MASK[i%HASH_CYCLE_LEN];
    }

    inserthashmask_const
}

fn get_copyhashmask_constants() -> Vec<BaseElement> {
    let mut copyhashmask_const = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];
    for i in 0..(HASH_CYCLE_LEN)*(SBALLEND){
        copyhashmask_const[i] = BaseElement::ONE - HASH_CYCLE_MASK[i%HASH_CYCLE_LEN];
    }

    copyhashmask_const
}
