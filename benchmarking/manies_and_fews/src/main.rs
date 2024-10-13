use palette_vec::{AutoMemoryOptimizationPolicyNever, OutPalVec, PalVec};

use clap::Parser;

#[derive(Parser)]
#[command(color = clap::ColorChoice::Auto)]
struct CommandLineSettings {
    #[arg(long)]
    many_instance_count: usize,

    #[arg(long)]
    few_instance_count: usize,

    #[arg(long)]
    how_many_manies: usize,
}

fn main() {
    let settings = CommandLineSettings::parse();

    struct Composition {
        instance_counts: Vec<usize>,
    }

    for how_many_fews in 0..100 {
        let manies = std::iter::repeat(settings.many_instance_count).take(settings.how_many_manies);
        let fews = std::iter::repeat(settings.few_instance_count).take(how_many_fews);
        let composition = Composition {
            instance_counts: manies.chain(fews).collect(),
        };

        let mut simple_pal_vec = PalVec::new();
        let mut out_pal_vec: OutPalVec<_, AutoMemoryOptimizationPolicyNever> = OutPalVec::new();

        for (element, instance_count) in composition.instance_counts.iter().copied().enumerate() {
            simple_pal_vec.push(element, instance_count);
            out_pal_vec.push(element, instance_count);
        }

        out_pal_vec.perform_memory_opimization();

        println!(
            "{}, {}",
            simple_pal_vec.used_memory(),
            out_pal_vec.used_memory()
        );
    }
}
