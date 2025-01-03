use super::dataset::Dataset;
use super::split_criteria::gini_coefficient_split_feature;
use super::split_criteria::mean_squared_error_split_feature;
use super::split_criteria::SplitFunction;
use super::split_criteria::SplitResult;
use super::utils;
use rand::rngs::StdRng;
use rand::seq::SliceRandom;
use rand::SeedableRng;
use rayon::prelude::*;
use std::cmp::Ordering::Equal;
use std::fmt::Debug;
use std::fmt::Formatter;

use pyo3::prelude::*;

/// Represents the decision tree model. Each node represents a split on a feature.
#[pyclass]
pub struct DecisionTree {
    // I just made this public for now, or I can change the DecisionTree internally to hdo the traversal
    pub tree: Tree,
}

/// Possible options for training the model.
#[derive(Clone, Copy)]
pub struct TrainOptions {
    /// Minimum number of samples required to be at a leaf node. default: 1
    min_samples_leaf: i32,
    /// Maximum depth of the tree. default: 10
    max_depth: i32,
    max_features: i32,
}

impl TrainOptions {
    /// Returns the default options for training a model.
    pub fn default_options(num_features: i32) -> TrainOptions {
        TrainOptions {
            max_depth: 10,
            min_samples_leaf: 1,
            max_features: num_features,
        }
    }
}

/// Methods for training and predicting with a decision tree. These methods are exposed to python.
#[pymethods]
impl DecisionTree {

    /// Trains a decision tree for regression.
    /// A regression tree uses the mean squared error as the split criterion.
    #[staticmethod]
    pub fn train_reg(
        train: &Dataset,
        max_depth: Option<i32>,
        min_samples_leaf: Option<i32>,
        max_features: Option<i32>,
        random_state: Option<u64>,
    ) -> DecisionTree {
        let mut rng = utils::get_rng(random_state, 0);
        let default_train_options = TrainOptions::default_options(train.feature_names.len() as i32);
        let params = TrainOptions {
            max_depth: max_depth.unwrap_or(default_train_options.max_depth),
            min_samples_leaf: min_samples_leaf.unwrap_or(default_train_options.min_samples_leaf),
            max_features: max_features.unwrap_or(default_train_options.max_features),
        };

        DecisionTree {
            tree: Tree::fit(
                &train,
                0,
                params,
                mean_squared_error_split_feature,
                &mut rng,
            ),
        }
    }

    /// Trains a decision tree for classification problem.
    /// A classification tree uses the gini coefficient as the split criterion.
    #[staticmethod]
    pub fn train_clf(
        train: &Dataset,
        max_depth: Option<i32>,
        min_samples_leaf: Option<i32>,
        max_features: Option<i32>,
        random_state: Option<u64>,
    ) -> DecisionTree {
        let mut rng = utils::get_rng(random_state, 0);
        let default_train_options = TrainOptions::default_options(train.feature_names.len() as i32);
        let params = TrainOptions {
            max_depth: max_depth.unwrap_or(default_train_options.max_depth),
            min_samples_leaf: min_samples_leaf.unwrap_or(default_train_options.min_samples_leaf),
            max_features: max_features.unwrap_or(default_train_options.max_features),
        };
        DecisionTree {
            tree: Tree::fit(&train, 0, params, gini_coefficient_split_feature, &mut rng),
        }
    }

    /// Predicts the target for a given dataset.
    pub fn predict(&self, test: &Dataset) -> Vec<f32> {
        self.tree.predict(test)
    }
}

fn split_dataset(split: &SplitResult, dataset: &Dataset) -> (Dataset, Dataset) {
    let mut left_dataset = dataset.clone_without_data();
    let mut right_dataset = dataset.clone_without_data();

    let best_feature_sorter =
        permutation::sort_by(&dataset.feature_matrix[split.col_index], |a, b| {
            a.partial_cmp(b).unwrap_or(Equal)
        });

    for i in 0..dataset.feature_names.len() {
        let sorted_feature = best_feature_sorter.apply_slice(&dataset.feature_matrix[i]);

        let mut first_half = sorted_feature.clone();
        let second_half = first_half.split_off(split.row_index);

        left_dataset.feature_matrix.push(first_half);
        let first = left_dataset.feature_matrix[i][0];
        left_dataset.feature_uniform[i] =
            left_dataset.feature_matrix[i].iter().all(|&x| x == first);
        right_dataset.feature_matrix.push(second_half);
        let first = right_dataset.feature_matrix[i][0];
        right_dataset.feature_uniform[i] =
            right_dataset.feature_matrix[i].iter().all(|&x| x == first);
    }

    let (_, sorted_target) = utils::sort_two_vectors(
        &dataset.feature_matrix[split.col_index],
        &dataset.target_vector,
    );

    let mut first_half = sorted_target;
    let second_half = first_half.split_off(split.row_index);

    left_dataset.target_vector = first_half;
    right_dataset.target_vector = second_half;

    (left_dataset, right_dataset)
}

fn should_stop(options: TrainOptions, depth: i32, ds: &Dataset) -> bool {
    let max_depth_reached = depth == options.max_depth;
    let min_samples_reached = options.min_samples_leaf > ds.n_samples() as i32 / 2;
    let uniform_features = ds.feature_uniform.iter().all(|&x| x);
    let one_sample = ds.n_samples() == 1;

    max_depth_reached || min_samples_reached || uniform_features || one_sample
}

// -------------------------------------
// Base Tree implementation

type NodeId = usize;
type FeatureIndex = usize;

/// An arena-based tree implementation. Each node is stored in a vector and the children are accessed by index.
///
/// Having all the nodes in a vector allows for a more cache-friendly implementation. And accessing
/// them by index allows to avoid borrow checker issues related to having recursive data structures.
pub struct Tree {
    pub root: NodeId,
    pub nodes: Vec<Node>,
    pub feature_names: Vec<String>,
}

#[derive(Debug)]
pub enum Node {
    Leaf(Leaf),
    Branch(Branch),
}

#[derive(PartialEq, Debug)]
pub struct Leaf {
    pub prediction: f32,
    pub samples: usize,
}

#[derive(PartialEq, Debug)]
pub struct Branch {
    pub feature: FeatureIndex,
    pub threshold: f32,
    pub left: NodeId,
    pub right: NodeId,
    pub samples: usize,
    pub prediction: f32,
}

impl Node {
    fn new_leaf(prediction: f32, samples: usize) -> Self {
        Node::Leaf(Leaf::new(prediction, samples))
    }
    fn samples(&self) -> usize {
        match self {
            Node::Leaf(leaf) => leaf.samples,
            Node::Branch(branch) => branch.samples,
        }
    }

    // Mohanna: Added these two new functions for checking the type of a node
    // Function to check if the node is a Branch
    pub fn is_branch(&self) -> bool {
        matches!(self, Node::Branch(_))
    }

    // Function to check if the node is a Leaf
    pub fn is_leaf(&self) -> bool {
        matches!(self, Node::Leaf(_))
    }
}

impl Leaf {
    fn new(prediction: f32, samples: usize) -> Self {
        Leaf {
            prediction,
            samples,
        }
    }
}

impl Tree {
    fn new<S: Into<String>>(feature_names: Vec<S>) -> Self {
        Tree {
            root: 0,
            nodes: Vec::new(),
            feature_names: feature_names.into_iter().map(|x| x.into()).collect(),
        }
    }

    fn new_from_split(
        &self,
        left: NodeId,
        right: NodeId,
        split: SplitResult,
        feature_name: &str,
    ) -> Node {
        Node::Branch(Branch {
            prediction: split.prediction,
            samples: self.nodes[left].samples() + self.nodes[right].samples(),
            threshold: split.split,
            feature: self
                .feature_names
                .iter()
                .position(|x| x == feature_name)
                .unwrap(),
            left,
            right,
        })
    }

    fn print(&self) {
        self.print_node(self.root, 0);
    }

    fn print_node(&self, node: NodeId, depth: usize) {
        match &self.nodes[node] {
            Node::Leaf(l) => {
                println!(
                    "{:indent$}|-> Leaf: pred: {}, N: {}",
                    "",
                    l.prediction,
                    l.samples,
                    indent = depth * 4
                );
            }
            Node::Branch(b) => {
                println!(
                    "{:indent$}-> Branch: feat: {}, th: {}, N: {}, pred: {}",
                    "",
                    self.feature_names[b.feature],
                    b.threshold,
                    b.samples,
                    b.prediction,
                    indent = depth * 4
                );
                self.print_node(b.left, depth + 1);
                self.print_node(b.right, depth + 1);
            }
        }
    }

    fn set_root(&mut self, node_id: NodeId) {
        self.root = node_id;
    }

    fn add_node(&mut self, node: Node) -> NodeId {
        self.nodes.push(node);
        self.nodes.len() - 1
    }

    fn predict(&self, test: &Dataset) -> Vec<f32> {
        let feature_matrix = self.reindex_features(&test);

        let mut predictions = Vec::with_capacity(test.n_samples());
        let mut nodes: Vec<NodeId> = Vec::new();
        for i in 0..test.n_samples() {
            nodes.push(self.root);
            while let Some(node) = nodes.pop() {
                match &self.nodes[node] {
                    Node::Leaf(l) => {
                        predictions.push(l.prediction);
                    }
                    Node::Branch(b) => {
                        if feature_matrix[b.feature][i] < b.threshold {
                            nodes.push(b.left);
                        } else {
                            nodes.push(b.right);
                        }
                    }
                }
            }
            nodes.clear();
        }
        predictions
    }

    fn reindex_features<'a>(&self, ds: &'a Dataset) -> Vec<&'a Vec<f32>> {
        let mut feature_indexes = Vec::with_capacity(self.feature_names.len());
        for feature in &self.feature_names {
            let index = ds.feature_names.iter().position(|x| x == feature);
            match index {
                Some(index) => feature_indexes.push(index),
                None => panic!("Feature {} not found in tree", feature),
            };
        }

        let mut feature_matrix = Vec::with_capacity(self.feature_names.len());
        for i in 0..self.feature_names.len() {
            feature_matrix.push(&ds.feature_matrix[feature_indexes[i]]);
        }
        feature_matrix
    }

    fn fit(
        train: &Dataset,
        depth: i32,
        train_options: TrainOptions,
        split_feature: SplitFunction,
        rng: &mut StdRng,
    ) -> Self {
        let mut tree = Tree::new(train.feature_names.clone());
        let root = tree.fit_node(train, depth, train_options, split_feature, rng);
        tree.set_root(root);
        tree
    }

    fn fit_node(
        &mut self,
        train: &Dataset,
        depth: i32,
        train_options: TrainOptions,
        split_feature: SplitFunction,
        rng: &mut StdRng,
    ) -> NodeId {
        if should_stop(train_options, depth, train) {
            let leaf = self.add_node(Node::new_leaf(
                utils::float_avg(&train.target_vector),
                train.n_samples(),
            ));
            return leaf;
        }

        let mut best_feature = SplitResult::new_max_loss();
        let mut feature_indexes = (0..train.feature_names.len()).collect::<Vec<usize>>();
        feature_indexes.shuffle(rng);
        let max_features = train_options.max_features;
        let selected_feature_indexes = feature_indexes[0..max_features as usize].to_vec();

        for i in selected_feature_indexes {
            if train.feature_uniform[i] {
                continue;
            }

            let split = split_feature(
                i,
                &train.feature_names[i],
                train_options.min_samples_leaf,
                &train.feature_matrix[i],
                &train.target_vector,
            );

            if split.loss < best_feature.loss {
                best_feature = split;
            }
        }

        let (left_ds, right_ds) = split_dataset(&best_feature, train);

        let left_child = self.fit_node(&left_ds, depth + 1, train_options, split_feature, rng);
        let right_child = self.fit_node(&right_ds, depth + 1, train_options, split_feature, rng);

        let name = &train.feature_names[best_feature.col_index];
        let node = self.new_from_split(left_child, right_child, best_feature, name);
        let node_id = self.add_node(node);
        node_id
    }
}

impl Debug for Tree {
    fn fmt(&self, _f: &mut Formatter<'_>) -> std::fmt::Result {
        self.print();
        Ok(())
    }
}

impl PartialEq for Tree {
    fn eq(&self, other: &Self) -> bool {
        let mut nodes_self = vec![self.root];
        let mut nodes_other = vec![other.root];

        while let Some(node) = nodes_self.pop() {
            let other_n = nodes_other.pop();
            if other_n.is_none() {
                return false;
            }
            let o = other_n.unwrap();
            match &self.nodes[node] {
                Node::Leaf(l) => match &other.nodes[o] {
                    Node::Leaf(l2) if l2 == l => {
                        continue;
                    }
                    _ => return false,
                },
                Node::Branch(b) => match &other.nodes[o] {
                    Node::Branch(b2) if b2 == b => {
                        nodes_self.push(b.left);
                        nodes_self.push(b.right);
                        nodes_other.push(b2.left);
                        nodes_other.push(b2.right);
                    }
                    _ => return false,
                },
            }
        }
        return true;
    }
}

// -------------------------------------

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_predict() {
        let dataset = Dataset::read_csv("datasets/toy_test.csv", ";");

        let mut tree = Tree::new(vec!["feature_a"]);
        let left = tree.add_node(Node::new_leaf(1., 1));
        let right = tree.add_node(Node::new_leaf(0., 1));
        let root = tree.add_node(Node::Branch(Branch {
            feature: 0,
            threshold: 2.,
            prediction: 0.5,
            samples: 2,
            left,
            right,
        }));
        tree.set_root(root);

        let dt = DecisionTree { tree };

        let expected = Dataset::read_csv("datasets/toy_test_predict.csv", ";");
        let pred = dt.predict(&dataset);
        assert_eq!(expected.target_vector, pred);
    }
}