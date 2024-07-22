use crate::{
    patch::{Hunk, HunkRange, Line, Patch},
    range::{DiffRange, SliceLike},
    utils::Classifier,
};
use std::{cmp, ops};

mod cleanup;
mod myers;

#[cfg(test)]
mod tests;

// TODO determine if this should be exposed in the public API
#[allow(dead_code)]
#[derive(Debug, PartialEq, Eq)]
enum Diff<'a, T: ?Sized> {
    Equal(&'a T),
    Delete(&'a T),
    Insert(&'a T),
}

impl<T: ?Sized> Copy for Diff<'_, T> {}

impl<T: ?Sized> Clone for Diff<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T> From<DiffRange<'a, 'a, T>> for Diff<'a, T>
where
    T: ?Sized + SliceLike,
{
    fn from(diff: DiffRange<'a, 'a, T>) -> Self {
        match diff {
            DiffRange::Equal(range, _) => Diff::Equal(range.as_slice()),
            DiffRange::Delete(range) => Diff::Delete(range.as_slice()),
            DiffRange::Insert(range) => Diff::Insert(range.as_slice()),
        }
    }
}

/// what kind of unambiguity:
/// `None` ~ so ambiguous aka normal
/// `OnlyForwardPatch` ~ the generated unified diff will be unambiguous
/// `BothForwardAndReversedPatches` ~ implies `OnlyForwardPatch` and the reversed patch of it is also unambiguous which typically means the context length is increased even more to make this happen in the case the normal patch added a new spot that the reverse will have to avoid.
#[derive(Debug)]
pub enum Unambiguous {
    None,
    OnlyForwardPatch,
    BothForwardAndReversedPatches,
}

/// A collection of options for modifying the way a diff is performed
#[derive(Debug)]
pub struct DiffOptions {
    compact: bool,
    unambiguous: Unambiguous,
    context_len: usize,
    pub quiet: bool,
}

const MAX_CONTEXT_LENGTH_TO_DISAMBIGUATE: usize = 30;

impl DiffOptions {
    /// Construct a new `DiffOptions` with default settings
    ///
    /// ## Defaults
    /// * context_len = 3
    pub fn new() -> Self {
        Self {
            compact: true,
            unambiguous: Unambiguous::BothForwardAndReversedPatches,
            context_len: 3,
            quiet: true,
        }
    }

    /// if true, the generated patch will have hunks, that independently and also during patch application on the same original file, cannot be applied to different spots, in other words: if more spots were created during applying the previous hunks, but also if each hunk alone is applied to the original file, then trying to reapply the same hunk will always fail instead of finding another spot for it and succeed.
    /// This is done by increasing context length (currently for the whole patch, tho ideally FIXME: for only the problematic hunk!) as needed to fulfil all that unambiguity.
    /// Obviously this isn't enough to do in the 'diff', so 'patch' itself must also ensure unambiguity when applying it to a modified original which clearly could've added new spots for any of the hunks.
    pub fn set_unambiguous(&mut self, unambiguous: Unambiguous) -> &mut Self {
        self.unambiguous = unambiguous;
        self
    }

//    /// if true, it acts like gnu diff or git diff would normally do, and generate ambiguous patch(es) whose hunks can be possibly reapplied and thus can land in the wrong spot in a future modified original file. See the description for `set_unambiguous`
//    pub fn set_ambiguous(&mut self, ambiguous: bool) -> &mut Self {
//        self.unambiguous = !ambiguous;
//        self
//    }

    /// Set the number of context lines that should be used when producing a patch
    pub fn set_context_len(&mut self, context_len: usize) -> &mut Self {
        self.context_len = context_len;
        self
    }

    /// Enable/Disable diff compaction. Compaction is a post-processing step which attempts to
    /// produce a prettier diff by reducing the number of edited blocks by shifting and merging
    /// edit blocks.
    // TODO determine if this should be exposed in the public API
    #[allow(dead_code)]
    fn set_compact(&mut self, compact: bool) -> &mut Self {
        self.compact = compact;
        self
    }

    // TODO determine if this should be exposed in the public API
    #[allow(dead_code)]
    fn diff<'a>(&self, original: &'a str, modified: &'a str) -> Vec<Diff<'a, str>> {
        let solution = myers::diff(original.as_bytes(), modified.as_bytes());

        let mut solution = solution
            .into_iter()
            .map(|diff_range| diff_range.to_str(original, modified))
            .collect();

        if self.compact {
            cleanup::compact(&mut solution);
        }

        solution.into_iter().map(Diff::from).collect()
    }

    /// Produce a Patch between two texts based on the configured options
    pub fn create_patch<'a>(&self, original: &'a str, modified: &'a str) -> Patch<'a, str> {
        let mut patch: Patch<str>;
        let mut context_len = self.context_len;
        let mut classifier = Classifier::default();
        let (old_lines, old_ids) = classifier.classify_lines(original);
        let (new_lines, new_ids) = classifier.classify_lines(modified);

        let solution = self.diff_slice(&old_ids, &new_ids);

        loop {
            let hunks = to_hunks(&old_lines, &new_lines, &solution, context_len);
            //eprintln!("Hunks: {:?}, original: '{}', mod: '{}'", hunks, original, modified);
            //doneFIXME: try each hunk independently, if it succeeds applying more than once TODO: increase context only for that hunk(somehow) while regenerating the patch!
            patch = Patch::new(Some("original"), Some("modified"), hunks);
            match self.unambiguous {
                Unambiguous::None => {
                    // if ambiguous, or
                    break;
                },
                _ => {
                    if original.is_empty() || modified.is_empty() {
                        // if either inputs are empty
                        // trying to disambiguate will fail and reach MAX_CONTEXT_LENGTH_TO_DISAMBIGUATE
                        // plus, it doesn't make sense to do.
                        break;
                    }
                    //else carry on, because we have some unambiguity to ensure!
                }
            }//match
            let patched = crate::apply(original, &patch, /*unambiguous:*/ true);
            //TODO: detect here or inside apply() ? if any hunks succeeded, while unambiguous is true!
            if patched.is_err() {
                //increase context length for the entire patch(FIXME: only for the specific hunk, but beware hunks can be merged compared to a previous lower context length, so hunks count can change with increase in context!) and see if it's still ambiguous
                context_len += 1;
                if context_len > MAX_CONTEXT_LENGTH_TO_DISAMBIGUATE {
                    panic!("!! Failed to disambiguately generate patch due to reached max context length of '{}' and the patch was still ambiguous!", MAX_CONTEXT_LENGTH_TO_DISAMBIGUATE);
                    /* The correct word is "disambiguately."

                    - **Disambiguate** is the verb meaning to make something clear by removing ambiguity.
                    - **Disambiguation** is the noun form, referring to the process of removing ambiguity.
                    - **Disambiguately** is the adverb form, describing an action done in a way that removes ambiguity.

                    So, you would use "disambiguately" when describing an action performed in a manner that clarifies or removes ambiguity.
                                        */
                }
            } else {
                // it applied, unambiguously
                // now let's see if what we patched is same as our initial modified file/contents
                if patched.ok().unwrap() != modified {
                    panic!("The generated patch applied on the original file, failed to reconstruct the modified file!");
                } else {
                    //if it is same, let's try to get back to our original!
                    let reversed_patch_should_be_unambiguous:bool=match self.unambiguous {
                        Unambiguous::OnlyForwardPatch => false,
                        Unambiguous::BothForwardAndReversedPatches => true,
                        Unambiguous::None => unreachable!("bad coding"),
                    };//match
                    let expected_original=crate::apply(modified, &patch.reverse(), reversed_patch_should_be_unambiguous);
                    match expected_original {
                        Err(e) => {
                            //FIXME: this isn't in sync with the create_patch_bytes() implementation!
                            panic!("Failed to apply the reversed patch on the modified file, error: '{}'", e);
                        },
                        Ok(orig) => {
                            if original != orig {
                                panic!("The reversed patch applied on the modified file, failed to reconstruct the original!");
                            }
                        }
                    }
                }
                break;
            }
        } //loop
        return patch;
    }

//    pub fn create_patch2<'a, T>(&self, original: &'a T, modified: &'a T) -> Patch<'a, T>
//    where
//        T: AsRef<[u8]> + ToOwned + ?Sized,
//    {
//        let mut patch: Patch<'a, T>;
//        let mut context_len = self.context_len;
//        let mut classifier = Classifier::default();
//
//        let (old_lines, old_ids) = classifier.classify_lines(original.as_ref());
//        let (new_lines, new_ids) = classifier.classify_lines(modified.as_ref());
//
//        let solution = self.diff_slice(&old_ids, &new_ids);
//
//        loop {
//            let hunks = to_hunks(&old_lines, &new_lines, &solution, context_len);
//            use std::borrow::Cow;
//            patch = Patch::new(
//                Some(Cow::Borrowed(original)),
//                Some(Cow::Borrowed(modified)),
//                hunks,
//            );
//            if !self.unambiguous || original.as_ref().is_empty() || modified.as_ref().is_empty() {
//                break;
//            }
//            let patched = crate::apply(original.as_ref(), &patch, true);
//            if patched.is_err() {
//                context_len += 1;
//                if context_len > MAX_CONTEXT_LENGTH_TO_DISAMBIGUATE {
//                    panic!("!! Failed to disambiguately generate patch due to reached max context length of '{}' and the patch was still ambiguous!", MAX_CONTEXT_LENGTH_TO_DISAMBIGUATE);
//                }
//            } else {
//                break;
//            }
//        }
//        patch
//    }

    /// Create a patch between two potentially non-utf8 texts
    pub fn create_patch_bytes<'a>(
        &self,
        original: &'a [u8],
        modified: &'a [u8],
    ) -> Patch<'a, [u8]> {
        self.create_patch_bytes_with_labels(original, modified, &b"original"[..], &b"modified"[..])
    }

    /// Create a patch between two potentially non-utf8 texts
    pub fn create_patch_bytes_with_labels<'a>(
        &self,
        original: &'a [u8],
        modified: &'a [u8],
        label_original: &'a [u8],
        label_modified: &'a [u8],
    ) -> Patch<'a, [u8]> {
        let mut patch: Patch<'a, [u8]>;
        let mut context_len = self.context_len;
        //let mod_clone=Vec::from(modified);

        let mut classifier = Classifier::default();
        let (old_lines, old_ids) = classifier.classify_lines(original);
        let (new_lines, new_ids) = classifier.classify_lines(modified);

        let solution = self.diff_slice(&old_ids, &new_ids);

        loop {
            let hunks = to_hunks(&old_lines, &new_lines, &solution, context_len);
            //patch = Patch::new(Some(&b"original"[..]), Some(&b"modified"[..]), hunks);
            patch = Patch::new(Some(label_original), Some(label_modified), hunks);
            match self.unambiguous {
                Unambiguous::None => {
                    break;
                },
                _ => {
                    if original.is_empty() || modified.is_empty() {
                        break;
                    }
                    //else carry on, because we have some unambiguity to ensure!
                }
            }//match
            // generate forward patch unambiguously
            let patched = crate::apply_bytes(original, &patch, /*unambiguous:*/ true);
            //TODO: detect here or inside apply_bytes() ? if any hunks succeeded, while unambiguous is true!
            if patched.is_err() {
                //increase context length for the entire patch(FIXME: only for the specific hunk, but beware hunks can be merged compared to a previous lower context length, so hunks count can change with increase in context!) and see if it's still ambiguous
                context_len += 1;
                if !self.quiet {
                    eprintln!("Failed to apply forward patch unambiguously, next retrying to generate the patch with bigger context length of '{}' lines.", context_len);
                }
                if context_len > MAX_CONTEXT_LENGTH_TO_DISAMBIGUATE {
                    panic!("!! Failed to disambiguately generate patch due to reached max context length of '{}' and the patch was still ambiguous!", MAX_CONTEXT_LENGTH_TO_DISAMBIGUATE);
                }
            } else {
                // it applied, unambiguously
                // now let's see if what we patched is same as our initial modified file/contents
                if patched.ok().unwrap() != modified {
                    panic!("The generated patch applied on the original file, failed to reconstruct the modified file!");
                } else {
                    //if it is same, let's try to get back to our original!
                    let reversed_patch=patch.reverse();
                    //assert_eq!(modified, mod_clone);
                    //FIXME: using 'false' for unambiguous application here because this reversed patch sometimes fails to unambiguously apply, and it's unclear if it shouldn't. Hmm, well if I wanted to unambiguously undo it, then I guess it should work.
                    let reversed_patch_should_be_unambiguous:bool=match self.unambiguous {
                        Unambiguous::OnlyForwardPatch => false,
                        Unambiguous::BothForwardAndReversedPatches => true,
                        Unambiguous::None => unreachable!("bad coding"),
                    };//match
                    let expected_original=crate::apply_bytes(modified, &reversed_patch, reversed_patch_should_be_unambiguous);
                    match expected_original {
                        Err(e) => {
                            let err=format!("Failed to apply the reversed patch, unambiguously?('{}'), on the modified file, error: '{}'.", reversed_patch_should_be_unambiguous, e);
                            if !reversed_patch_should_be_unambiguous {
                                panic!("{}", err);
                            }
                            //std::fs::write("/tmp/FAILpatch.orig", &original).unwrap();
                            //std::fs::write("/tmp/FAILpatch.patch", &patch.to_bytes()).unwrap();
                            //std::fs::write("/tmp/FAILpatch.patched", &modified).unwrap();
                            //std::fs::write("/tmp/FAILpatch.rev.patch", &reversed_patch.to_bytes()).unwrap();
                            //panic!("{}, saved the relevants as /tmp/FAIL*", err);
                            context_len += 1;
                            if !self.quiet {
                                eprintln!("{}, attempting to redo with increased context length aka lines of '{}'.", err, context_len);
                            }
                            if context_len > MAX_CONTEXT_LENGTH_TO_DISAMBIGUATE {
                                panic!("!! Failed to unambiguously generate reversed patch due to reached max context length of '{}' and the reversed patch was still ambiguous!", MAX_CONTEXT_LENGTH_TO_DISAMBIGUATE);
                            } else {
                                //continue the loop
                                continue;
                            }
                        },
                        Ok(orig) => {
                            if original != orig {
                                panic!("The reversed patch applied on the modified file, failed to reconstruct the original!");
                            } else {
                                break;
                            }
                        }
                    }
                }
                //break;
                #[allow(unreachable_code)]
                {
                    unreachable!();
                }
            }
        } //loop
        return patch;
    }

    pub(crate) fn diff_slice<'a, T: PartialEq>(
        &self,
        old: &'a [T],
        new: &'a [T],
    ) -> Vec<DiffRange<'a, 'a, [T]>> {
        let mut solution = myers::diff(old, new);

        if self.compact {
            cleanup::compact(&mut solution);
        }

        solution
    }
}//DiffOptions

impl Default for DiffOptions {
    fn default() -> Self {
        Self::new()
    }
}

// TODO determine if this should be exposed in the public API
#[allow(dead_code)]
fn diff<'a>(original: &'a str, modified: &'a str) -> Vec<Diff<'a, str>> {
    DiffOptions::default().diff(original, modified)
}

/// Create a patch between two texts.
///
/// ```
/// # use diffy::create_patch;
/// let original = "\
/// I am afraid, however, that all I have known - that my story - will be forgotten.
/// I am afraid for the world that is to come.
/// Afraid that my plans will fail.
/// Afraid of a doom worse than the Deepness.
/// ";
///
/// let modified = "\
/// I am afraid, however, that all I have known - that my story - will be forgotten.
/// I am afraid for the world that is to come.
/// Afraid that Alendi will fail.
/// Afraid of a doom brought by the Deepness.
/// ";
///
/// let expected = "\
/// --- original
/// +++ modified
/// @@ -1,4 +1,4 @@
///  I am afraid, however, that all I have known - that my story - will be forgotten.
///  I am afraid for the world that is to come.
/// -Afraid that my plans will fail.
/// -Afraid of a doom worse than the Deepness.
/// +Afraid that Alendi will fail.
/// +Afraid of a doom brought by the Deepness.
/// ";
///
/// let patch = create_patch(original, modified);
/// assert_eq!(patch.to_string(), expected);
/// ```
pub fn create_patch<'a>(original: &'a str, modified: &'a str) -> Patch<'a, str> {
    DiffOptions::default().create_patch(original, modified)
}

/// Create a patch between two potentially non-utf8 texts
pub fn create_patch_bytes<'a>(original: &'a [u8], modified: &'a [u8]) -> Patch<'a, [u8]> {
    DiffOptions::default().create_patch_bytes(original, modified)
}

fn to_hunks<'a, T: ?Sized>(
    lines1: &[&'a T],
    lines2: &[&'a T],
    solution: &[DiffRange<[u64]>],
    context_len: usize,
) -> Vec<Hunk<'a, T>> {
    let edit_script = build_edit_script(solution);

    let mut hunks = Vec::new();

    let mut idx = 0;
    while let Some(mut script) = edit_script.get(idx) {
        let start1 = script.old.start.saturating_sub(context_len);
        let start2 = script.new.start.saturating_sub(context_len);

        let (mut end1, mut end2) = calc_end(
            context_len,
            lines1.len(),
            lines2.len(),
            script.old.end,
            script.new.end,
        );

        let mut lines = Vec::new();

        // Pre-context
        for line in lines2.get(start2..script.new.start).into_iter().flatten() {
            lines.push(Line::Context(*line));
        }

        loop {
            // Delete lines from text1
            for line in lines1.get(script.old.clone()).into_iter().flatten() {
                lines.push(Line::Delete(*line));
            }

            // Insert lines from text2
            for line in lines2.get(script.new.clone()).into_iter().flatten() {
                lines.push(Line::Insert(*line));
            }

            if let Some(s) = edit_script.get(idx + 1) {
                // Check to see if we can merge the hunks
                let start1_next =
                    cmp::min(s.old.start, lines1.len() - 1).saturating_sub(context_len);
                if start1_next < end1 {
                    // Context lines between hunks
                    for (_i1, i2) in (script.old.end..s.old.start).zip(script.new.end..s.new.start)
                    {
                        if let Some(line) = lines2.get(i2) {
                            lines.push(Line::Context(*line));
                        }
                    }

                    // Calc the new end
                    let (e1, e2) = calc_end(
                        context_len,
                        lines1.len(),
                        lines2.len(),
                        s.old.end,
                        s.new.end,
                    );

                    end1 = e1;
                    end2 = e2;
                    script = s;
                    idx += 1;
                    continue;
                }
            }

            break;
        }

        // Post-context
        for line in lines2.get(script.new.end..end2).into_iter().flatten() {
            lines.push(Line::Context(*line));
        }

        let len1 = end1 - start1;
        let old_range = HunkRange::new(if len1 > 0 { start1 + 1 } else { start1 }, len1);

        let len2 = end2 - start2;
        let new_range = HunkRange::new(if len2 > 0 { start2 + 1 } else { start2 }, len2);

        hunks.push(Hunk::new(old_range, new_range, None, lines));
        idx += 1;
    }

    hunks
}

fn calc_end(
    context_len: usize,
    text1_len: usize,
    text2_len: usize,
    script1_end: usize,
    script2_end: usize,
) -> (usize, usize) {
    let post_context_len = cmp::min(
        context_len,
        cmp::min(
            text1_len.saturating_sub(script1_end),
            text2_len.saturating_sub(script2_end),
        ),
    );

    let end1 = script1_end + post_context_len;
    let end2 = script2_end + post_context_len;

    (end1, end2)
}

#[derive(Debug)]
struct EditRange {
    old: ops::Range<usize>,
    new: ops::Range<usize>,
}

impl EditRange {
    fn new(old: ops::Range<usize>, new: ops::Range<usize>) -> Self {
        Self { old, new }
    }
}

fn build_edit_script<T>(solution: &[DiffRange<[T]>]) -> Vec<EditRange> {
    let mut idx_a = 0;
    let mut idx_b = 0;

    let mut edit_script: Vec<EditRange> = Vec::new();
    let mut script = None;

    for diff in solution {
        match diff {
            DiffRange::Equal(range1, range2) => {
                idx_a += range1.len();
                idx_b += range2.len();
                if let Some(script) = script.take() {
                    edit_script.push(script);
                }
            }
            DiffRange::Delete(range) => {
                match &mut script {
                    Some(s) => s.old.end += range.len(),
                    None => {
                        script = Some(EditRange::new(idx_a..idx_a + range.len(), idx_b..idx_b));
                    }
                }
                idx_a += range.len();
            }
            DiffRange::Insert(range) => {
                match &mut script {
                    Some(s) => s.new.end += range.len(),
                    None => {
                        script = Some(EditRange::new(idx_a..idx_a, idx_b..idx_b + range.len()));
                    }
                }
                idx_b += range.len();
            }
        }
    }

    if let Some(script) = script.take() {
        edit_script.push(script);
    }

    edit_script
}
