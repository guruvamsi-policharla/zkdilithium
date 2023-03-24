use super::{
    BaseElement, ThinDilAir, FieldElement, ProofOptions, Prover, aux_trace_table::RapTraceTable, TRACE_WIDTH, N, M, air::PublicInputs,
    HASH_CYCLE_LEN, HASH_STATE_WIDTH, HASH_RATE_WIDTH, NUM_HASH_ROUNDS, HASH_DIGEST_WIDTH, ZIND, QIND, RIND, CIND, 
    CTILDEIND, HASHIND,  ZRANGEIND, QRANGEIND, RRANGEIND, ZRANGE, QRANGE, RRANGE, BETA, TAU, PADDED_TRACE_LENGTH, 
    SWAPDECIND, SBALLEND, WIND, QWIND, SIGNIND, ZLIMIT, WLOWIND, WBIND, WHIGHIND, GAMMA2, WLOWLIMIT, 
    WLOWRANGEIND, WLOWRANGE, WHIGHSHIFT, WHIGHRANGEIND, WHIGHRANGE, K, PIT_START, PIT_LEN, COM_START, HTR, COM_END};

use crate::utils::poseidon_23_spec::{self};

// Dilithium PROVER
// ================================================================================================

pub struct ThinDilProver {
    options: ProofOptions,
    z: [[BaseElement; N]; K],
    w: [[BaseElement; N]; K],
    qw: [[BaseElement; N]; K],
    ctilde: [BaseElement; HASH_DIGEST_WIDTH],
    m: [BaseElement; 12],
    com_r: [BaseElement; 12]
}

impl ThinDilProver {
    pub fn new(options: ProofOptions, z: [[BaseElement; N]; K], w: [[BaseElement; N]; K],  qw: [[BaseElement; N]; K], ctilde: [BaseElement; HASH_DIGEST_WIDTH], m: [BaseElement; 12], com_r: [BaseElement; 12]) -> Self {
        Self {options, z, w, qw, ctilde, m, com_r}
    }

    // Builds an execution trace for verifying dilithium signatures
    pub fn build_trace(&self) -> RapTraceTable<BaseElement> {
        let mut trace = RapTraceTable::new(TRACE_WIDTH, PADDED_TRACE_LENGTH);
        
        trace.fill(
            // Initialize the registers with CTILDE and push CTILDE into the HASH_RATE_REGISTERS
            |state| {
                // ctilde
                for i in 0..HASH_DIGEST_WIDTH {
                    state[CTILDEIND+i] = self.ctilde[i];
                }

                // hash_space with domain separation
                state[HASHIND] = BaseElement::from(2u32);
                for i in 0..HASH_DIGEST_WIDTH{
                    state[HASHIND + i + 1] += state[CTILDEIND + i];
                }
            },

            |step, state| {
                let cycle_pos = step % HASH_CYCLE_LEN;
                let _cycle_num = step / HASH_CYCLE_LEN;

                let base: u32 = (N-TAU + step-(HASH_CYCLE_LEN)) as u32;
                
                // apply poseidon round in all but the last round of HASH_CYCLE
                if cycle_pos < NUM_HASH_ROUNDS {
                    poseidon_23_spec::apply_round(&mut state[HASHIND..(HASHIND+3*HASH_STATE_WIDTH)], step);
                }

                // Ballsample section
                if step < (HASH_CYCLE_LEN)*(SBALLEND)-1{
                    // Hashing to compute randomness used in BallSample
                    if cycle_pos == NUM_HASH_ROUNDS {
                        // Computing random value % basei where basei runs from N-TAU..N and storing in RIND, QIND
                        for i in 0..HASH_CYCLE_LEN{
                            let x = state[HASHIND+i].to_string().parse::<u32>().unwrap();
                            
                            let basei = base + (i+1) as u32;
                            
                            state[QIND+i] = BaseElement::new(x/basei);
                            state[RIND+i] = BaseElement::new(x%basei);    
                        }

                        // Extracting bits for sign flips
                        bitdec(
                            state[HASHIND+HASH_CYCLE_LEN].to_string().parse::<u64>().unwrap() % 2u64.pow(HASH_CYCLE_LEN as u32),
                            &mut state[SIGNIND..SIGNIND+HASH_CYCLE_LEN] 
                        );

                        // Below is needed because rotate_left happens at every step and we don't want to do it whenever hashing is complete
                        state[QIND..QIND+HASH_CYCLE_LEN].rotate_right(1);
                        state[RIND..RIND+HASH_CYCLE_LEN].rotate_right(1);
                        state[SIGNIND..SIGNIND+HASH_CYCLE_LEN].rotate_right(1);
                    }

                    // Starts at the end of first round of hashing above. Then we start swapping and negation
                    if step >= HASH_CYCLE_LEN-1 {
                        // The base goes from 216 to 255
                        state[QIND..QIND+HASH_CYCLE_LEN].rotate_left(1);
                        state[RIND..RIND+HASH_CYCLE_LEN].rotate_left(1);
                        state[SIGNIND..SIGNIND+HASH_CYCLE_LEN].rotate_left(1);
                        
                        bitdec(state[QIND].to_string().parse::<u64>().unwrap(), &mut state[QRANGEIND..(QRANGEIND+QRANGE)]);
                        bitdec(state[RIND].to_string().parse::<u64>().unwrap(), &mut state[RRANGEIND..(RRANGEIND+RRANGE)]);

                        bitdec(state[QIND].to_string().parse::<u64>().unwrap() + (M/(base+1)) as u64, &mut state[QRANGEIND+QRANGE..(QRANGEIND+2*QRANGE)]);
                        bitdec(state[RIND].to_string().parse::<u64>().unwrap() + 256 - (base+1) as u64, &mut state[RRANGEIND+RRANGE..(RRANGEIND+2*RRANGE)]);

                        // Hashing ctilde to ball
                        // Swapping and negating entries of c as described in Dilithium.v3
                        let sel = state[RIND];

                        state[CIND + (base) as usize] = state[CIND + sel.to_string().parse::<usize>().unwrap()];
                        state[CIND + sel.to_string().parse::<usize>().unwrap()] = BaseElement::ONE - BaseElement::new(2)*state[SIGNIND];

                        // Resetting the SWAPDEC registers to 0
                        for i in 0..N{
                            state[SWAPDECIND+i] = BaseElement::ZERO;
                        }
                        state[SWAPDECIND + state[RIND].to_string().parse::<usize>().unwrap()] = BaseElement::ONE;
                    }
                }

                // Opening a hash-based commitment -- signature on com = H(m||com_r)
                // the constraints will be enforced as follows
                // assert that the last HASH_STATE_WIDTH-HASH_RATE_WIDTH registers match H(rho||t)
                // assert that the first 12 registers are H(rho||t) + m
                // the next 12 registers dont need any constraints as the prover is allowed to choose any com_r
                if step == COM_START-1 {
                    // insert m and com_r
                    // m and com_r are each 12 field elements perfectly filling up HASH_RATE_WIDTH
                    for j in 0..HASH_STATE_WIDTH {
                        state[HASHIND+j] = BaseElement::from(HTR[j]);
                    }

                    for j in 0..12 {
                        state[HASHIND+j] += self.m[j];
                        state[HASHIND+12+j] += self.com_r[j];
                    }
                }

                if step == COM_END-1 {
                    // Reset HASH_STATE-HAS_RATE to 0 and leave mu=H(HTR||com(m;com_r)) in HASH_RATE
                    for j in HASH_RATE_WIDTH..HASH_STATE_WIDTH{
                        state[HASHIND+j] = BaseElement::ZERO;
                    }
                }

                // PIT section                
                let zlimitf = BaseElement::from(ZLIMIT);
                let wlowlimitf = BaseElement::from(WLOWLIMIT);
                let whighshiftf = BaseElement::from(WHIGHSHIFT);
                let betaf = BaseElement::from(BETA);
                if step == PIT_START-1 {
                    // Reset HASH_STATE to 0
                    for j in HASH_STATE_WIDTH..3*HASH_STATE_WIDTH{
                        state[HASHIND+j] = BaseElement::ZERO;
                    }
                }

                if step >= PIT_START-1 {
                    // Helper variables
                    let poly_cycle = (step+1 - PIT_START) / HASH_CYCLE_LEN;
                    let polycycle_pos = (step+1 - PIT_START) % HASH_CYCLE_LEN;

                    // Inserting Z, W and QW polynomials in the first 6 rows of each HASH_CYCLE
                    // edge_case: Note that each HASH_CYCLE consumes 24 coefficients but N*K % 24 = 16
                    // hence in the last HASH_CYCLE we need to pad with 8 zero elements
                    if step < PIT_START-1 + PIT_LEN-4 {
                        if polycycle_pos < HASH_CYCLE_LEN-2{
                            let poly_ind = poly_cycle*(HASH_CYCLE_LEN-2) + polycycle_pos;
                            for j in 0..K{
                                state[ZIND+j] = self.z[j][poly_ind];
                                state[QWIND+j] = self.qw[j][poly_ind];
                                state[WIND+j] = self.w[j][poly_ind];
                            }
                        }

                        // Populating WHIGH with HASH_RATE_WIDTH entries at the end of every cycle
                        // these will be rotated to ensure the same values are used in decomposition check are hashed
                        if polycycle_pos == 0 {
                            // Check if it's the last cycle
                            let jj_end: usize = if poly_cycle == N/(HASH_CYCLE_LEN-2) {HASH_RATE_WIDTH/K-2} else {HASH_RATE_WIDTH/K};

                            for jj in 0..jj_end {
                                for j in 0..K {
                                    let (_,w1) = wdec(self.w[j][poly_cycle*(HASH_CYCLE_LEN-2) + jj].to_string().parse::<i64>().unwrap());
                                    state[WHIGHIND+jj*K+j] = BaseElement::from((w1.rem_euclid((M).into())) as u64);
                                }
                            }

                            // make last 12 entries of WHIGH 0
                            for jj in jj_end..HASH_RATE_WIDTH/K {
                                for j in 0..K {
                                    state[WHIGHIND+jj*K+j] = BaseElement::ZERO;
                                }
                            }

                            // Absorb values into sponge
                            for j in 0..HASH_RATE_WIDTH{
                                state[HASHIND+j] += state[WHIGHIND+j];
                            }
                        }
                    }

                    /////////////////////////////////////////////////////////////////////
                    // Post processing after insertion --- bitdec, wdec, rotations, poseidon round
                    
                    // Rotate W and C by 4 and 1 positions to the left respectively at first HASH_CYCLE_LEN-2 rows in each cycle
                    if step >= PIT_START{
                        let hashcycle_pos = (step-PIT_START)%HASH_CYCLE_LEN;

                        if hashcycle_pos < HASH_CYCLE_LEN-2{                        
                            state[WHIGHIND..(WHIGHIND+HASH_RATE_WIDTH)].rotate_left(4);
                            state[CIND..(CIND+N)].rotate_left(1);
                        }
                    } 

                    // Bit decomposition of the FOUR elements in ZIND..ZIND+K
                    for j in 0..K{
                        bitdec(
                            (state[ZIND+j]+zlimitf).to_string().parse::<u64>().unwrap(),
                            &mut state[ZRANGEIND+(2*j)*ZRANGE..(ZRANGEIND+(2*j+1)*ZRANGE)]
                        );
                        bitdec(
                            (state[ZIND+j]+zlimitf+betaf).to_string().parse::<u64>().unwrap(),
                            &mut state[ZRANGEIND+(2*j+1)*ZRANGE..(ZRANGEIND+(2*j+2)*ZRANGE)]
                        );
                    }

                    // decompse w into low bits
                    for j in 0..K{
                        let windj = state[WIND+j].to_string().parse::<i64>().unwrap();
                        let (w0,w1) = wdec(windj);
                        let w2 = if windj== (M as i64-GAMMA2 as i64) {1} else {0};
                        state[WBIND+j] = BaseElement::from(w2 as u8); // w2 is always a bit
                        state[WLOWIND+j] = BaseElement::from((w0.rem_euclid(M.into())) as u64);
                        if w2==1 {
                            println!("{},{},{}", w0,w1,w2);
                        }
                    }
                    
                    // WLOW rangeproof
                    // Since the ranges line up with powers of two we only have one range proof
                    for j in 0..K{
                        bitdec(
                            (state[WLOWIND+j]+wlowlimitf).to_string().parse::<u64>().unwrap(),
                            &mut state[WLOWRANGEIND+(j)*WLOWRANGE..(WLOWRANGEIND+(j+1)*WLOWRANGE)]
                        );
                    } 

                    // WHIGH rangeproof
                    for j in 0..K{
                        bitdec(
                            (state[WHIGHIND+j]).to_string().parse::<u64>().unwrap(),
                            &mut state[WHIGHRANGEIND+(2*j)*WHIGHRANGE..(WHIGHRANGEIND+(2*j+1)*WHIGHRANGE)]
                        );
                        bitdec(
                            (state[WHIGHIND+j]+whighshiftf).to_string().parse::<u64>().unwrap(),
                            &mut state[WHIGHRANGEIND+(2*j+1)*WHIGHRANGE..(WHIGHRANGEIND+(2*j+2)*WHIGHRANGE)]
                        );
                    }
                    /////////////////////////////////////////////////////////////////////////////////   
                }

                // Artifact of winterfell. Used to prevent constant polynomial when interpolating
                if step==PADDED_TRACE_LENGTH-2 {
                    for i in 0..TRACE_WIDTH{
                        state[i] = BaseElement::new(123 as u32);
                    }
                }
            },
        );

        trace
    }
}

impl Prover for ThinDilProver {
    type BaseField = BaseElement;
    type Air = ThinDilAir;
    type Trace = RapTraceTable<BaseElement>;

    fn get_pub_inputs(&self, _trace: &Self::Trace) -> PublicInputs {
        PublicInputs{m: self.m}
    }
    fn options(&self) -> &ProofOptions {
        &self.options
    }
}

fn bitdec(mut x: u64, bits: &mut [BaseElement]) {
    let mut b;
    
    // Assertion checking that length of bits is large enough to decompose x
    debug_assert!((x as f32).log2() <= bits.len() as f32, "Value: {} did not fit in {} bits", x, bits.len());
    
    // Placing the bits of x into the bits array in little endian form
    for i in 0..bits.len() {
        b = x % 2;
        bits[i] = BaseElement::new(b as u32);
        x = x/2;
    }
}

// decomposes elements into high and low bits
fn wdec(x: i64) -> (i64, i64) {
    let gamma2: i64 = GAMMA2 as i64;
    let mut x0: i64 = x % (2*gamma2);
    
    if x0 > gamma2 {
        x0 -= 2*gamma2;
    }
    if (x -x0) == ((M-1) as i64){
        return (x0-1,0)
    }

    return (x0, (x as i64-x0)/(2*gamma2))
}

#[allow(unused)]
fn print_field_slice(v: &[BaseElement], n: usize){
    print!("[");
    for i in 0..n{
        print!("{}, ", v[i]);
    }
    println!("]");
}