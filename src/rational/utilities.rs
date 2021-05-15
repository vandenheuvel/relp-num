use std::cmp::Ordering;

use crate::non_zero::NonZero;

pub(crate) fn merge_sparse_indices<I: Ord, T: NonZero + Eq>(
    left: impl Iterator<Item=(I, T)> + Sized,
    right: impl Iterator<Item=(I, T)> + Sized,
    operation: impl Fn(T, T) -> T,
    operation_left: impl Fn(T) -> T,
    operation_right: impl Fn(T) -> T,
) -> Vec<(I, T)> {
    let mut result = Vec::with_capacity(left.size_hint().0.max(right.size_hint().0));

    let mut left = left.peekable();
    let mut right = right.peekable();

    while let (Some((left_index, _)), Some((right_index, _))) = (left.peek(), right.peek()) {
        match left_index.cmp(&right_index) {
            Ordering::Less => {
                let (index, value) = left.next().unwrap();
                result.push((index, operation_left(value)));
            },
            Ordering::Equal => {
                let (left_index, left_value) = left.next().unwrap();
                let operation_result = operation(left_value, right.next().unwrap().1);
                if operation_result.is_not_zero() {
                    result.push((left_index, operation_result));
                }
            },
            Ordering::Greater => {
                let (index, value) = right.next().unwrap();
                result.push((index, operation_right(value)));
            },
        }
    }

    for (left_index, value) in left {
        result.push((left_index, operation_left(value)))
    }
    for (right_index, value) in right {
        result.push((right_index, operation_right(value)))
    }

    result
}

#[cfg(test)]
mod test {
    use std::convert::identity;
    use std::ops::Add;

    use crate::rational::utilities::merge_sparse_indices;

    #[test]
    fn test_merge_sparse_indices() {
        // Empty
        let left: Vec<(i8, i16)> = vec![];
        let right = vec![];

        let result = merge_sparse_indices(left.into_iter(), right.into_iter(), Add::add, identity, identity);
        let expected = vec![];
        assert_eq!(result, expected);

        // One empty
        let left: Vec<(i8, i16)> = vec![(2, 1)];
        let right = vec![];

        let result = merge_sparse_indices(left.into_iter(), right.into_iter(), Add::add, identity, identity);
        let expected = vec![(2, 1)];
        assert_eq!(result, expected);

        // Not related
        let left = vec![(1, 6)].into_iter();
        let right = vec![(4, 9)].into_iter();

        let result = merge_sparse_indices(left, right, Add::add, identity, identity);
        let expected = vec![(1, 6), (4, 9)];
        assert_eq!(result, expected);

        // Same index
        let left = vec![(1, 6)].into_iter();
        let right = vec![(1, 9)].into_iter();

        let result = merge_sparse_indices(left, right, Add::add, identity, identity);
        let expected = vec![(1, 15)];
        assert_eq!(result, expected);

        // Alternating
        let left = vec![(1, 6), (3, 4)].into_iter();
        let right = vec![(2, 9)].into_iter();

        let result = merge_sparse_indices(left, right, Add::add, identity, identity);
        let expected = vec![(1, 6), (2, 9), (3, 4)];
        assert_eq!(result, expected);
    }
}
