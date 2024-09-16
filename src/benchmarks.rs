use palette_vec::{AutoMemoryOptimizationPolicyNever, OutPalVec, PalVec};

fn main() {
    struct Composition {
        instance_counts: Vec<usize>,
    }

    let composition = Composition {
        instance_counts: vec![1000, 1000, 1000, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    };

    let mut simple_pal_vec = PalVec::new();
    let mut out_pal_vec: OutPalVec<_, AutoMemoryOptimizationPolicyNever> = OutPalVec::new();

    for (element, instance_count) in composition.instance_counts.iter().copied().enumerate() {
        for _ in 0..instance_count {
            simple_pal_vec.push(element);
            out_pal_vec.push(element);
        }
    }

    out_pal_vec.perform_memory_opimization();

    println!(
        "{}, {}",
        simple_pal_vec.used_memory(),
        out_pal_vec.used_memory()
    );
}
