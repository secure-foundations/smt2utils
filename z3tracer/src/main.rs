// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

#![forbid(unsafe_code)]

use z3tracer::{report::*, syntax::*, Model, ModelConfig};

use multiset::HashMultiSet;
use petgraph::graph::Graph;
use petgraph::visit::DfsPostOrder;
use petgraph::Direction;
use plotters::prelude::*;
use std::{collections::*, io::Write, path::PathBuf};
use structopt::StructOpt;

/// Test utility for the parsing and the analysis of Z3 log files.
#[derive(Debug, StructOpt)]
#[structopt(name = "z3tracer")]
struct Options {
    #[structopt(flatten)]
    config: ModelConfig,

    /// Shortcut for all the --plot-* options.
    #[structopt(long)]
    plot_all: bool,

    /// Output a PNG file (for each input file) to represent quantifier instantiations
    /// over time.
    #[structopt(long)]
    plot_instantiations: bool,

    /// Output a PNG file (for each input file) to represent "user" quantifier
    /// instantiations (defined based on a prefix of their name).
    #[structopt(long)]
    plot_user_instantiations: bool,

    /// Output a PNG file (for each input file) to represent backtracking (aka "scoped" computations).
    #[structopt(long)]
    plot_scopes: bool,

    /// Output a PNG file (for each input file) to represent conflicts on top of quantifier instantiations.
    #[structopt(long)]
    plot_conflicts: bool,

    /// Output a PNG file (for each input file) to represent conflicts on top of user quantifier instantiations.
    #[structopt(long)]
    plot_user_conflicts: bool,

    /// Output a PNG file (for each input file) to represent the causal graph between quantifier instantiations.
    #[structopt(long)]
    plot_instantiation_graph: bool,

    /// Output a PNG file (for each input file) to represent the causal graph between
    /// quantifier instantiations as well as conflict.
    #[structopt(long)]
    plot_instantiation_graph_with_conflicts: bool,

    /// Whether to prune nodes that are not "user" instantiations in
    /// --plot-instantiation-graph*. Note: Depending on the connectivity of the graph,
    /// this may lose transitive dependencies between user nodes.
    #[structopt(long)]
    keep_only_user_instantiations_in_graphs: bool,

    /// Use a single node for all conflicts in graph.
    #[structopt(long)]
    merge_conflicts_in_graphs: bool,

    /// How to select "user" instantiations.
    #[structopt(long, default_value = "outputbpl")]
    user_instantiation_prefix: String,

    /// How many instantiations to represent.
    #[structopt(long, default_value = "10")]
    keep_top_instantiations: usize,

    /// Path to the Z3 log files.
    #[structopt(parse(from_os_str))]
    inputs: Vec<PathBuf>,
}

// Compute top instantiated terms and retrieve the "timestamps" at which instantiations occur for each of the top terms.
fn get_instantiations(model: &Model) -> Vec<(String, Vec<usize>)> {
    IntoIterSorted::from(model.most_instantiated_terms())
        .map(|(_count, id)| {
            let mut timestamps = model
                .term_data(&id)
                .unwrap()
                .instantiation_timestamps
                .clone();
            timestamps.sort_unstable();
            let name = model.id2name(&id).unwrap_or_else(|| "??".to_string());
            (name, timestamps)
        })
        .collect()
}

fn get_dependency_graph(
    model: &Model,
    with_conflicts: bool,
    keep_only_user_instantiations: Option<&str>,
    merge_conflicts_in_graphs: bool,
) -> petgraph::Graph<String, String> {
    // Define nodes as the names of QIs (e.g. the names of quantified expressions in the source code).
    let nodes = model
        .instantiations()
        .iter()
        .filter_map(|(k, _)| {
            if model.key2name(k).is_some() {
                model.key2name(k)
            } else {
                None
            }
        })
        .collect::<HashSet<_>>();

    // Define weighted edges (counting dependencies in the original graph of QIs).
    let edges = {
        let mut map = HashMap::new();
        for (k, qi) in model.instantiations() {
            if let Some(name) = model.key2name(k) {
                let deps = map.entry(name).or_insert_with(HashMultiSet::new);
                for qik in &qi.qi_deps {
                    if let Some(n) = model.key2name(&qik.key) {
                        deps.insert(n);
                    }
                }
            }
        }
        map
    };

    // Translate the graph into `petgraph` for drawing purposes.
    let mut graph = Graph::<String, String>::new();

    let mut pg_nodes = HashMap::new();
    for node in &nodes {
        if let Some(prefix) = keep_only_user_instantiations {
            if !node.starts_with(prefix) {
                continue;
            }
        }
        let n = graph.add_node(node.to_string());
        pg_nodes.insert(node.to_string(), n);
    }

    for (n, d) in edges.iter() {
        if let Some(n) = pg_nodes.get(n) {
            for m in d.distinct_elements() {
                let c = d.count_of(m);
                if let Some(m) = pg_nodes.get(m) {
                    graph.add_edge(*n, *m, c.to_string());
                }
            }
        }
    }

    if with_conflicts {
        if merge_conflicts_in_graphs {
            // Adding one node for all conflicts.
            let n0 = graph.add_node("all conflicts".into());
            let mut outgoing = HashMultiSet::new();
            for c in model.conflicts() {
                for d in &c.qi_deps {
                    if let Some(m) = model.key2name(&d.key) {
                        outgoing.insert(m)
                    }
                }
            }
            for m in outgoing.distinct_elements() {
                let c = outgoing.count_of(m);
                if let Some(m) = pg_nodes.get(m) {
                    graph.add_edge(n0, *m, c.to_string());
                }
            }
        } else {
            // Adding conflicts separately (with multiplicities as weights)
            for c in model.conflicts() {
                let mut outgoing = HashMultiSet::new();
                for d in &c.qi_deps {
                    if let Some(m) = model.key2name(&d.key) {
                        outgoing.insert(m)
                    }
                }
                if outgoing.is_empty() {
                    // Skip dependency-less conflicts.
                    continue;
                }
                let n = graph.add_node(format!("conflict@{}", c.timestamp));
                for m in outgoing.distinct_elements() {
                    let c = outgoing.count_of(m);
                    if let Some(m) = pg_nodes.get(m) {
                        graph.add_edge(n, *m, c.to_string());
                    }
                }
            }
        }
    }
    graph
}

fn main() {
    let mut options = Options::from_args();
    if options.plot_all {
        options.plot_instantiations = true;
        options.plot_user_instantiations = true;
        options.plot_scopes = true;
        options.plot_conflicts = true;
        options.plot_user_conflicts = true;
        options.plot_instantiation_graph = true;
        options.plot_instantiation_graph_with_conflicts = true;
    }
    for input in &options.inputs {
        let file_name = input.to_str().unwrap().to_string();
        eprintln!("Processing {}", file_name);
        let model = process_file(options.config.clone(), &input).unwrap();
        eprintln!("Done processing {}", file_name);
        eprintln!("# Terms: {}", model.terms().len());
        //println!("Terms: {:?}", model.terms());
        for term in model.terms() {
            println!("Term: {:?}", term);
        }
        eprintln!("# Instantiations: {}", model.instantiations().len());
        //println!("Instantiations: {:?}", model.instantiations());
        for inst in model.instantiations() {
            println!("Instantiation: {:?}", inst);
        }

        let mut term_blame = HashMap::new();
        let quantifier_inst_matches =
            model
                .instantiations()
                .iter()
                .filter(|(_, quant_inst)| match quant_inst.frame {
                    QiFrame::Discovered { .. } => false,
                    QiFrame::NewMatch { .. } => true,
                });

        for (qi_key, quant_inst) in quantifier_inst_matches.clone() {
            for inst in &quant_inst.instances {
                for node_ident in &inst.enodes {
                    term_blame.insert(node_ident, qi_key);
                }
            }
        }
        println!("term_blame: {:?}", term_blame);

        let mut graph = Graph::<&str, u32>::new();
        let origin = graph.add_node("Denver");
        let destination_1 = graph.add_node("San Diego");
        let destination_2 = graph.add_node("New York");

        println!("{:?}, {:?}, {:?}", origin, destination_1, destination_2);

        graph.extend_with_edges(&[
            (origin, destination_1, 250),
            (destination_1, destination_2, 1099),
        ]);

        //        let mut dfs = DfsPostOrder::new(&graph, origin);
        //        for qi_root in graph.externals(Direction::Incoming) {
        //            dfs.move_to(qi_root);  // Keep visit map from the previous DFS traversal
        //            while let Some(index) = dfs.next(&graph) {
        //                println!("Visiting {:?}", index);
        //            }
        //        }

        // Create a graph over QuantifierInstances,
        // where U->V if U produced an e-term that
        // triggered U
        let mut graph = Graph::<QiKey, ()>::new();
        let mut node_map = HashMap::new();
        for (qi_key, _) in quantifier_inst_matches.clone() {
            let index = graph.add_node(*qi_key);
            node_map.insert(qi_key, index);
        }
        for (qi_key, quant_inst) in quantifier_inst_matches.clone() {
            match &quant_inst.frame {
                QiFrame::Discovered { .. } => {
                    panic!("We filtered out all of the Discovered instances already!")
                }
                QiFrame::NewMatch { used: u, .. } => {
                    for used in u.iter() {
                        match used {
                            MatchedTerm::Trigger(t) => {
                                match term_blame.get(&t) {
                                    None => println!("Nobody to blame for {:?}", t),
                                    Some(qi_responsible) =>
                                    // Quantifier instantiation that produced the triggering term
                                    {
                                        let qi_responsible_index =
                                            node_map.get(qi_responsible).unwrap();
                                        let qi_key_index = node_map.get(qi_key).unwrap();
                                        graph.add_edge(*qi_responsible_index, *qi_key_index, ());
                                        ()
                                    }
                                }
                            }
                            MatchedTerm::Equality(t1, t2) => (), // TODO: What happens in this case?
                        }
                    }
                }
            }
        }

        // Compute the in-degree of each QuantifierInstance
        let mut in_degree: HashMap<QiKey, u64> = HashMap::new();
        let (some_qi_key, _) = quantifier_inst_matches.clone().next().unwrap();
        let some_index = node_map.get(&some_qi_key).unwrap();
        let mut dfs = DfsPostOrder::new(&graph, *some_index);
        for qi_root in graph.externals(Direction::Incoming) {
            // For each root of the graph
            dfs.move_to(qi_root); // Keep visit map from the previous DFS traversal
            while let Some(index) = dfs.next(&graph) {
                let qi_key = &graph[index];
                match in_degree.get_mut(&graph[index]) {
                    None => {
                        in_degree.insert(*qi_key, 1);
                        ()
                    }
                    Some(count) => *count += 1,
                }
            }
        }

        // Compute the cost of each QuantifierInstance
        let mut qi_cost: HashMap<QiKey, u64> = HashMap::new();
        let mut dfs = DfsPostOrder::new(&graph, *some_index);
        for qi_root in graph.externals(Direction::Incoming) {
            dfs.move_to(qi_root); // Keep visit map from the previous DFS traversal
            while let Some(index) = dfs.next(&graph) {
                let qi_key = &graph[index];
                let mut sum = 0;
                for neighbor in graph.neighbors_directed(index, Direction::Outgoing) {
                    let neighbor_key = &graph[neighbor];
                    sum +=
                        qi_cost.get(neighbor_key).unwrap() / in_degree.get(neighbor_key).unwrap();
                }
                qi_cost.insert(*qi_key, 1 + sum);
            }
        }

        // Finally, compute the cost of each quantifier
        let mut quant_cost: HashMap<Ident, u64> = HashMap::new();
        for (qi_key, quant_inst) in quantifier_inst_matches {
            let quant = quant_inst.frame.quantifier();
            let qi_cost = qi_cost.get(qi_key).unwrap();
            match quant_cost.get_mut(quant) {
                None => {
                    quant_cost.insert(quant.clone(), *qi_cost);
                    ()
                }
                Some(cost) => {
                    *cost += qi_cost;
                    ()
                }
            }
        }

        for (quant, cost) in &quant_cost {
            let term = model
                .term(&quant)
                .expect(format!("failed to find {:?}", quant).as_str());
            match term {
                Term::Quant { name, .. } => println!("Quant {} has cost {}", name, cost),
                //                    if name.starts_with(USER_QUANT_PREFIX) {
                //                        Some((name.clone(), count))
                //                    } else {
                //                        None
                //                    },
                _ => (),
            }
        }

        if !options.plot_instantiations
            && !options.plot_user_instantiations
            && !options.plot_scopes
            && !options.plot_conflicts
            && !options.plot_user_conflicts
            && !options.plot_instantiation_graph
            && !options.plot_instantiation_graph_with_conflicts
        {
            continue;
        }

        let instantiations = get_instantiations(&model);
        let user_instantiations = instantiations
            .clone()
            .into_iter()
            .filter(|(n, _)| n.starts_with(&options.user_instantiation_prefix))
            .collect::<Vec<_>>();
        let conflicts = model
            .conflicts()
            .map(|c| {
                (
                    c.timestamp,
                    c.qi_deps
                        .iter()
                        .map(|k| model.key2name(&k.key).unwrap_or_else(|| "??".to_string()))
                        .collect::<BTreeSet<_>>(),
                )
            })
            .collect::<Vec<_>>();

        if options.plot_instantiations {
            let path = std::path::PathBuf::from(file_name.clone() + ".qis.png");
            eprintln!(
                "Writing instantiation charts to {}",
                path.to_str().unwrap_or("")
            );
            let backend = BitMapBackend::new(&path, (1000, 800));
            let root = backend.into_drawing_area();
            plot_instantiations(
                root,
                &instantiations,
                "Top Quantifiers Instantiations",
                options.keep_top_instantiations,
            )
            .unwrap();
        }

        if options.plot_user_instantiations {
            let path = std::path::PathBuf::from(file_name.clone() + ".user_qis.png");
            eprintln!(
                "Writing user instantiation charts to {}",
                path.to_str().unwrap_or("")
            );
            let backend = BitMapBackend::new(&path, (1000, 800));
            let root = backend.into_drawing_area();
            plot_instantiations(
                root,
                &user_instantiations,
                "Top User Quantifiers Instantiations",
                options.keep_top_instantiations,
            )
            .unwrap();
        }

        if options.plot_scopes {
            let path = std::path::PathBuf::from(file_name.clone() + ".scopes.png");
            eprintln!("Writing scope charts to {}", path.to_str().unwrap_or(""));

            let scopes = model
                .scopes()
                .iter()
                .map(|s| (s.timestamp, s.level))
                .collect::<Vec<(usize, u64)>>();
            let backend = BitMapBackend::new(&path, (1000, 800));
            let root = backend.into_drawing_area();
            plot_scopes(root, &scopes, "Backtracking levels").unwrap();
        }

        if options.plot_conflicts {
            let path = std::path::PathBuf::from(file_name.clone() + ".conflicts.png");
            eprintln!("Writing conflict charts to {}", path.to_str().unwrap_or(""));

            let backend = BitMapBackend::new(&path, (1000, 800));
            let root = backend.into_drawing_area();
            plot_instantiations_with_conflicts(
                root,
                &instantiations,
                "Top Quantifiers Instantiations + Conflicts",
                options.keep_top_instantiations,
                &conflicts,
            )
            .unwrap();
        }

        if options.plot_user_conflicts {
            let path = std::path::PathBuf::from(file_name.clone() + ".user_conflicts.png");
            eprintln!(
                "Writing user conflict charts to {}",
                path.to_str().unwrap_or("")
            );

            let backend = BitMapBackend::new(&path, (1000, 800));
            let root = backend.into_drawing_area();
            plot_instantiations_with_conflicts(
                root,
                &user_instantiations,
                "Top User Quantifiers Instantiations + Conflicts",
                options.keep_top_instantiations,
                &conflicts,
            )
            .unwrap();
        }

        let keep_only_user_instantiations = if options.keep_only_user_instantiations_in_graphs {
            Some(options.user_instantiation_prefix.as_str())
        } else {
            None
        };

        if options.plot_instantiation_graph {
            let path = std::path::PathBuf::from(file_name.clone() + ".qis_graph.dot");
            eprintln!(
                "Writing dependency graph to {}",
                path.to_str().unwrap_or("")
            );

            let g = get_dependency_graph(&model, false, keep_only_user_instantiations, false);
            let mut f = std::fs::File::create(path.clone()).unwrap();
            writeln!(f, "{}", petgraph::dot::Dot::new(&g)).unwrap();

            std::process::Command::new("dot")
                .args(&["-O", "-Tpng", path.to_str().unwrap()])
                .status()
                .expect("Error running `dot` (is graphviz installed?)");
        }

        if options.plot_instantiation_graph_with_conflicts {
            let path = std::path::PathBuf::from(file_name.clone() + ".qis_and_conflicts_graph.dot");
            eprintln!(
                "Writing dependency graph with conflicts to {}",
                path.to_str().unwrap_or("")
            );

            let g = get_dependency_graph(
                &model,
                true,
                keep_only_user_instantiations,
                options.merge_conflicts_in_graphs,
            );
            let mut f = std::fs::File::create(path.clone()).unwrap();
            writeln!(f, "{}", petgraph::dot::Dot::new(&g)).unwrap();

            std::process::Command::new("dot")
                .args(&["-O", "-Tpng", path.to_str().unwrap()])
                .status()
                .expect("Error running `dot` (is graphviz installed?)");
        }
    }
}
