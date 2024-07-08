use crate::{
    patch::{Hunk, Line, Patch},
    utils::LineIter,
};
use std::{fmt, iter};

/// An error returned when [`apply`]ing a `Patch` fails
///
/// [`apply`]: fn.apply.html
#[derive(Debug)]
pub struct ApplyError(usize);

impl fmt::Display for ApplyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error applying hunk #{}", self.0)
    }
}

impl std::error::Error for ApplyError {}

#[derive(Debug)]
enum ImageLine<'a, T: ?Sized> {
    Unpatched(&'a T),
    Patched(&'a T),
}

impl<'a, T: ?Sized> ImageLine<'a, T> {
    fn inner(&self) -> &'a T {
        match self {
            ImageLine::Unpatched(inner) | ImageLine::Patched(inner) => inner,
        }
    }

    fn into_inner(self) -> &'a T {
        self.inner()
    }

    fn is_patched(&self) -> bool {
        match self {
            ImageLine::Unpatched(_) => false,
            ImageLine::Patched(_) => true,
        }
    }
}

impl<T: ?Sized> Copy for ImageLine<'_, T> {}

impl<T: ?Sized> Clone for ImageLine<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

/// Apply a `Patch` to a base image
///
/// ```
/// use diffy::{apply, Patch};
///
/// let s = "\
/// --- a/ideals
/// +++ b/ideals
/// @@ -1,4 +1,6 @@
///  First:
///      Life before death,
///      strength before weakness,
///      journey before destination.
/// +Second:
/// +    I will protect those who cannot protect themselves.
/// ";
///
/// let patch = Patch::from_str(s).unwrap();
///
/// let base_image = "\
/// First:
///     Life before death,
///     strength before weakness,
///     journey before destination.
/// ";
///
/// let expected = "\
/// First:
///     Life before death,
///     strength before weakness,
///     journey before destination.
/// Second:
///     I will protect those who cannot protect themselves.
/// ";
///
/// assert_eq!(apply(base_image, &patch, false).unwrap(), expected);
/// ```
pub fn apply(
    base_image: &str,
    patch: &Patch<'_, str>,
    unambiguous: bool,
) -> Result<String, ApplyError> {
    let mut image: Vec<_> = LineIter::new(base_image)
        .map(ImageLine::Unpatched)
        .collect();

    if unambiguous {
        for (i, hunk) in patch.hunks().iter().enumerate() {
            //unambiguously apply each hunk independently, on the original file.
            let mut fresh_image = image.clone();
            apply_hunk(&mut fresh_image, hunk, /*unambiguous:*/ true)
                .map_err(|_| ApplyError(i + 1))?;
        }
    }
    //if unambiguous and the above 'if for' succeeded, then the below cannot fail!
    //FIXME: ok, it could fail if any prev. hunks that got applied created a new place of a subsequent hunk to be applied to! thus now having 2 spots where it could apply!
    for (i, hunk) in patch.hunks().iter().enumerate() {
        let res = apply_hunk(&mut image, hunk, unambiguous).map_err(|_| ApplyError(i + 1));
        if let Err(e) = res {
            if !unambiguous {
                return Err(e);
            } else {
                //it's unambiguous
                panic!("apply str Should not have failed to apply, this means some coding logic error is afoot! err:'{}'",e);
            }
        }
    }

    Ok(image.into_iter().map(ImageLine::into_inner).collect())
}

/// Apply a non-utf8 `Patch` to a base image
pub fn apply_bytes(
    base_image: &[u8],
    patch: &Patch<'_, [u8]>,
    unambiguous: bool,
) -> Result<Vec<u8>, ApplyError> {
    let mut image: Vec<_> = LineIter::new(base_image)
        .map(ImageLine::Unpatched)
        .collect();

    if unambiguous {
        for (i, hunk) in patch.hunks().iter().enumerate() {
            //unambiguously apply each hunk independently, on the original file.
            let mut fresh_image = image.clone();
            apply_hunk(&mut fresh_image, hunk, /*unambiguous:*/ true)
                .map_err(|_| ApplyError(i + 1))?;
        }
    }
    //if unambiguous and the above 'if for' succeeded, then the below cannot fail!
    //FIXME: ok, it could fail if any prev. hunks that got applied created a new place of a subsequent hunk to be applied to! thus now having 2 spots where it could apply!
    for (i, hunk) in patch.hunks().iter().enumerate() {
        let res = apply_hunk(&mut image, hunk, unambiguous).map_err(|_| ApplyError(i + 1));
        if let Err(e) = res {
            if !unambiguous {
                // if ambiguous, error normally
                return Err(e);
            } else {
                //it's unambiguous
                panic!("apply bytes Should not have failed to apply, this means some coding logic error is afoot! actual err:'{}'",e);
            }
        }
    }

    Ok(image
        .into_iter()
        .flat_map(ImageLine::into_inner)
        .copied()
        .collect())
}

fn apply_hunk<'a, T: PartialEq + ?Sized>(
    image: &mut Vec<ImageLine<'a, T>>,
    hunk: &Hunk<'a, T>,
    unambiguous: bool,
) -> Result<(), ()> {
    // Find position
    // this errs out even if, unambiguous==true and hunk cannot be unambiguously applied! ie. if it applies in more than 1 place!
    let pos = find_position(image, hunk, unambiguous).ok_or(())?;
    //println!("preFound pos: {:?}", pos);

    // update image
    image.splice(
        pos..pos + pre_image_line_count(hunk.lines()),
        post_image(hunk.lines()).map(ImageLine::Patched),
    );

    if unambiguous {
        if let Some(_pos2) = find_position(image, hunk, /*unambiguous:*/ true) {
            // if we got here, we didn't have any other position to apply the hunk, before applying it!
            // but now that we've applied it, a new pos was created, due to applying it!
            //panic!("postFound pos: {:?} which means the hunk we just applied created a new position for itself within itself; or find_position() is coded wrongly!", pos2);
            return Err(());
        }
    }
    Ok(())
}

// Search in `image` for a palce to apply hunk.
// This follows the general algorithm (minus fuzzy-matching context lines) described in GNU patch's
// man page.
//
// It might be worth looking into other possible positions to apply the hunk to as described here:
// https://neil.fraser.name/writing/patch/
fn find_position<T: PartialEq + ?Sized>(
    image: &[ImageLine<T>],
    hunk: &Hunk<'_, T>,
    unambiguous: bool,
) -> Option<usize> {
    // In order to avoid searching through positions which are out of bounds of the image,
    // clamp the starting position based on the length of the image
    let pos = std::cmp::min(hunk.new_range().start().saturating_sub(1), image.len());

    // Create an iterator that starts with 'pos' and then interleaves
    // moving pos backward/foward by one.
    let backward = (0..pos).rev();
    let forward = pos + 1..image.len();

    if !unambiguous {
        //ambiguous, find&return only the first position, if any
        iter::once(pos)
            .chain(interleave(backward, forward))
            .find(|&pos| match_fragment(image, hunk.lines(), pos))
    } else {
        let elements: Vec<usize> = iter::once(pos)
            .chain(interleave(backward, forward))
            .filter(|&pos| match_fragment(image, hunk.lines(), pos))
            .collect();
        if elements.len() != 1 {
            // 0 or more than 1 positions found! pretend we found none

            //if elements.len() > 1 {
            //    println!("Found more than 1 positions for hunk, positions: {:?}", elements);
            //}

            None
        } else {
            // exactly 1 pos
            Some(elements[0])
        }
    }
}

fn pre_image_line_count<T: ?Sized>(lines: &[Line<'_, T>]) -> usize {
    pre_image(lines).count()
}

fn post_image<'a, 'b, T: ?Sized>(lines: &'b [Line<'a, T>]) -> impl Iterator<Item = &'a T> + 'b {
    lines.iter().filter_map(|line| match line {
        Line::Context(l) | Line::Insert(l) => Some(*l),
        Line::Delete(_) => None,
    })
}

fn pre_image<'a, 'b, T: ?Sized>(lines: &'b [Line<'a, T>]) -> impl Iterator<Item = &'a T> + 'b {
    lines.iter().filter_map(|line| match line {
        Line::Context(l) | Line::Delete(l) => Some(*l),
        Line::Insert(_) => None,
    })
}

fn match_fragment<T: PartialEq + ?Sized>(
    image: &[ImageLine<T>],
    lines: &[Line<'_, T>],
    pos: usize,
) -> bool {
    let len = pre_image_line_count(lines);

    let image = if let Some(image) = image.get(pos..pos + len) {
        image
    } else {
        return false;
    };

    // If any of these lines have already been patched then we can't match at this position
    if image.iter().any(ImageLine::is_patched) {
        return false;
    }

    pre_image(lines).eq(image.iter().map(ImageLine::inner))
}

#[derive(Debug)]
struct Interleave<I, J> {
    a: iter::Fuse<I>,
    b: iter::Fuse<J>,
    flag: bool,
}

fn interleave<I, J>(
    i: I,
    j: J,
) -> Interleave<<I as IntoIterator>::IntoIter, <J as IntoIterator>::IntoIter>
where
    I: IntoIterator,
    J: IntoIterator<Item = I::Item>,
{
    Interleave {
        a: i.into_iter().fuse(),
        b: j.into_iter().fuse(),
        flag: false,
    }
}

impl<I, J> Iterator for Interleave<I, J>
where
    I: Iterator,
    J: Iterator<Item = I::Item>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        self.flag = !self.flag;
        if self.flag {
            match self.a.next() {
                None => self.b.next(),
                item => item,
            }
        } else {
            match self.b.next() {
                None => self.a.next(),
                item => item,
            }
        }
    }
}
