use winter_utils::{collections::Vec, uninit_vector};
use winterfell::{
    math::{log2, FieldElement, StarkField},
    EvaluationFrame, Matrix, Trace, TraceInfo, TraceLayout,
};
use crate::starkpf::{HASH_CYCLE_LEN, CIND, ZIND, WIND, QWIND};

use super::{AUX_WIDTH, PIT_START, PIT_END};

pub const CAUX: usize = 0;
pub const ZAUX: usize = CAUX + 1;
pub const WAUX: usize = ZAUX + 4;
pub const QWAUX: usize = WAUX + 4;
pub const GAMMA: usize = QWAUX + 4;
pub const POLYMULTASSERT: usize = GAMMA + 1;

#[derive(Debug)]
pub struct RapTraceTable<B: StarkField> {
    layout: TraceLayout,
    trace: Matrix<B>,
    meta: Vec<u8>,
}

impl<B: StarkField> RapTraceTable<B> {
    pub fn new(width: usize, length: usize) -> Self {
        Self::with_meta(width, length, vec![])
    }

    pub fn with_meta(width: usize, length: usize, meta: Vec<u8>) -> Self {
        assert!(
            width > 0,
            "execution trace must consist of at least one column"
        );
        assert!(
            width <= TraceInfo::MAX_TRACE_WIDTH,
            "execution trace width cannot be greater than {}, but was {}",
            TraceInfo::MAX_TRACE_WIDTH,
            width
        );
        assert!(
            length >= TraceInfo::MIN_TRACE_LENGTH,
            "execution trace must be at least {} steps long, but was {}",
            TraceInfo::MIN_TRACE_LENGTH,
            length
        );
        assert!(
            length.is_power_of_two(),
            "execution trace length must be a power of 2"
        );
        assert!(
            log2(length) as u32 <= B::TWO_ADICITY,
            "execution trace length cannot exceed 2^{} steps, but was 2^{}",
            B::TWO_ADICITY,
            log2(length)
        );
        assert!(
            meta.len() <= TraceInfo::MAX_META_LENGTH,
            "number of metadata bytes cannot be greater than {}, but was {}",
            TraceInfo::MAX_META_LENGTH,
            meta.len()
        );

        let columns = unsafe { (0..width).map(|_| uninit_vector(length)).collect() };
        Self {
            layout: TraceLayout::new(width, [AUX_WIDTH], [1]),
            trace: Matrix::new(columns),
            meta,
        }
    }

    // DATA MUTATORS
    // --------------------------------------------------------------------------------------------
    pub fn fill<I, U>(&mut self, init: I, update: U)
    where
        I: Fn(&mut [B]),
        U: Fn(usize, &mut [B]),
    {
        let mut state = vec![B::ZERO; self.main_trace_width()];
        init(&mut state);
        self.update_row(0, &state);

        for i in 0..self.length() - 1 {
            update(i, &mut state);
            self.update_row(i + 1, &state);
        }
    }

    /// Updates a single row in the execution trace with provided data.
    pub fn update_row(&mut self, step: usize, state: &[B]) {
        self.trace.update_row(step, state);
    }

    // PUBLIC ACCESSORS
    // --------------------------------------------------------------------------------------------

    /// Returns the number of columns in this execution trace.
    pub fn width(&self) -> usize {
        self.main_trace_width()
    }

    /// Returns value of the cell in the specified column at the specified row of this trace.
    #[allow(unused)]
    pub fn get(&self, column: usize, step: usize) -> B {
        self.trace.get(column, step)
    }

    /// Reads a single row from this execution trace into the provided target.
    pub fn read_row_into(&self, step: usize, target: &mut [B]) {
        self.trace.read_row_into(step, target);
    }
}

// TRACE TRAIT IMPLEMENTATION
// ================================================================================================

impl<B: StarkField> Trace for RapTraceTable<B> {
    type BaseField = B;

    fn layout(&self) -> &TraceLayout {
        &self.layout
    }

    fn length(&self) -> usize {
        self.trace.num_rows()
    }

    fn meta(&self) -> &[u8] {
        &self.meta
    }

    fn read_main_frame(&self, row_idx: usize, frame: &mut EvaluationFrame<Self::BaseField>) {
        let next_row_idx = (row_idx + 1) % self.length();
        self.trace.read_row_into(row_idx, frame.current_mut());
        self.trace.read_row_into(next_row_idx, frame.next_mut());
    }

    fn main_segment(&self) -> &Matrix<B> {
        &self.trace
    }

    fn build_aux_segment<E>(
        &mut self,
        aux_segments: &[Matrix<E>],
        rand_elements: &[E],
    ) -> Option<Matrix<E>>
    where
        E: FieldElement<BaseField = Self::BaseField>,
    {
        if !aux_segments.is_empty() {
            return None;
        }

        let mut current_row = unsafe { uninit_vector(self.width()) };
        // let mut next_row = unsafe { uninit_vector(self.width()) };
        self.read_row_into(0, &mut current_row);
        let mut aux_columns = vec![vec![E::ZERO; self.length()]; self.aux_trace_width()];
        
        for i in 0..AUX_WIDTH{
            aux_columns[i][PIT_START] = E::ZERO;
        }
        aux_columns[GAMMA][PIT_START] = E::ONE;
        
        let mut gamma1 = E::ONE;

        for step in PIT_START..PIT_END {
            let matmul_step = step-PIT_START;
            let matmul_pos = (matmul_step) % HASH_CYCLE_LEN;

            self.read_row_into(step, &mut current_row);
            
            if matmul_pos < HASH_CYCLE_LEN - 2{
                // C eval
                aux_columns[CAUX][step+1] = aux_columns[CAUX][step] + gamma1*current_row[CIND].into();
                
                // Z eval
                for i in 0..4{
                    aux_columns[ZAUX+i][step+1] = aux_columns[ZAUX+i][step] + gamma1*current_row[ZIND+i].into();
                }

                // W eval
                for i in 0..4{
                    aux_columns[WAUX+i][step+1] = aux_columns[WAUX+i][step] + gamma1*current_row[WIND+i].into();
                }

                // QW eval
                for i in 0..4{
                    aux_columns[QWAUX+i][step+1] = aux_columns[QWAUX+i][step] + gamma1*current_row[QWIND+i].into();
                }

                // Maintain a column of powers of gamma1
                gamma1 *= rand_elements[0];
                aux_columns[GAMMA][step+1] = gamma1;
            } else {
                // Do nothing and simply copy values
                for i in 0..AUX_WIDTH {
                    aux_columns[i][step+1] = aux_columns[i][step];
                }
            }
            
        }

        Some(Matrix::new(aux_columns))
    }
}
