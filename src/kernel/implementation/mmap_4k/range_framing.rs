use vstd::prelude::*;

use crate::*;

use super::syscall_def::{
    mmap_4k_range_empty_from,
    mmap_4k_range_mapped_prefix,
};

verus! {

/// A fresh exact 4K insertion extends an already mapped range prefix by one.
///
/// This is a PageTable/Map framing fact, independent of any kernel operation.
pub(super) proof fn pagetable_4k_insert_advances_range_prefix_forall()
    ensures
        forall|
            pre: PageTable<PT_TYPE>,
            post: PageTable<PT_TYPE>,
            range: VaRange4K,
            i: int,
            entry: MapEntry,
            write: bool,
            execute_disable: bool,
        |
            #![trigger
                mmap_4k_range_mapped_prefix(
                    post,
                    &range,
                    i + 1,
                    write,
                    execute_disable,
                ),
                pre.mapping_4k().insert(
                    range.view().spec_index(i),
                    entry,
                )
            ]
            #![trigger
                post.mapping_4k().spec_index(
                    range.view().spec_index(i),
                ),
                pre.mapping_4k().insert(
                    range.view().spec_index(i),
                    entry,
                ),
                mmap_4k_range_mapped_prefix(
                    pre,
                    &range,
                    i,
                    write,
                    execute_disable,
                )
            ]
            pre.wf()
            && post.wf()
            && range.wf()
            && 0 <= i < range.len
            && post.kernel_l4_end == pre.kernel_l4_end
            && post.mapping_4k() == pre.mapping_4k().insert(
                range.view().spec_index(i),
                entry,
            )
            && post.mapping_2m() == pre.mapping_2m()
            && post.mapping_1g() == pre.mapping_1g()
            && entry.present
            && entry.write == write
            && entry.execute_disable == execute_disable
            && mmap_4k_range_mapped_prefix(
                pre,
                &range,
                i,
                write,
                execute_disable,
            )
            ==> mmap_4k_range_mapped_prefix(
                post,
                &range,
                i + 1,
                write,
                execute_disable,
            ),
{
    assert forall|
        pre: PageTable<PT_TYPE>,
        post: PageTable<PT_TYPE>,
        range: VaRange4K,
        i: int,
        entry: MapEntry,
        write: bool,
        execute_disable: bool,
    |
        #![trigger
            mmap_4k_range_mapped_prefix(
                post,
                &range,
                i + 1,
                write,
                execute_disable,
            ),
            pre.mapping_4k().insert(
                range.view().spec_index(i),
                entry,
            )
        ]
        #![trigger
            post.mapping_4k().spec_index(
                range.view().spec_index(i),
            ),
            pre.mapping_4k().insert(
                range.view().spec_index(i),
                entry,
            ),
            mmap_4k_range_mapped_prefix(
                pre,
                &range,
                i,
                write,
                execute_disable,
            )
        ]
        pre.wf()
        && post.wf()
        && range.wf()
        && 0 <= i < range.len
        && post.kernel_l4_end == pre.kernel_l4_end
        && post.mapping_4k() == pre.mapping_4k().insert(
            range.view().spec_index(i),
            entry,
        )
        && post.mapping_2m() == pre.mapping_2m()
        && post.mapping_1g() == pre.mapping_1g()
        && entry.present
        && entry.write == write
        && entry.execute_disable == execute_disable
        && mmap_4k_range_mapped_prefix(
            pre,
            &range,
            i,
            write,
            execute_disable,
        )
        implies mmap_4k_range_mapped_prefix(
            post,
            &range,
            i + 1,
            write,
            execute_disable,
        ) by {
        assert forall|j: int|
            #![trigger post.mapping_4k().dom().contains(
                range.view().spec_index(j),
            )]
            #![trigger post.mapping_4k().spec_index(
                range.view().spec_index(j),
            )]
            0 <= j < i + 1 implies {
                let va = range.view().spec_index(j);
                &&& post.mapping_4k().dom().contains(va)
                &&& post.mapping_4k().spec_index(va).present
                &&& post.mapping_4k().spec_index(va).write == write
                &&& post.mapping_4k().spec_index(va).execute_disable
                    == execute_disable
            } by {
                if j < i {
                    assert(range.view().spec_index(j)
                        != range.view().spec_index(i)) by { seq_index_lemma::<VAddr>(); };
                    assert(
                        post.mapping_4k().dom().contains(
                            range.view().spec_index(j),
                        ) == pre.mapping_4k().dom().contains(
                            range.view().spec_index(j),
                        )
                        && post.mapping_4k().spec_index(
                            range.view().spec_index(j),
                        ) == pre.mapping_4k().spec_index(
                            range.view().spec_index(j),
                        )
                    ) by { broadcast use vstd::map::group_map_lemmas; };
                } else {
                    assert(
                        post.mapping_4k().dom().contains(
                            range.view().spec_index(i),
                        )
                        && post.mapping_4k().spec_index(
                            range.view().spec_index(i),
                        ) == entry
                    ) by { broadcast use vstd::map::group_map_lemmas; };
                }
            };
    };
}

/// An exact insertion at the current range cursor preserves usability of the
/// strictly later addresses.
pub(super) proof fn pagetable_4k_insert_preserves_range_suffix_forall()
    ensures
        forall|
            pre: PageTable<PT_TYPE>,
            post: PageTable<PT_TYPE>,
            range: VaRange4K,
            i: int,
            insert_va: VAddr,
            entry: MapEntry,
        |
            #![trigger
                mmap_4k_range_empty_from(post, &range, i + 1),
                pre.mapping_4k().insert(insert_va, entry)
            ]
            #![trigger
                post.mapping_4k().spec_index(
                    range.view().spec_index(i),
                ),
                pre.mapping_4k().insert(insert_va, entry),
                mmap_4k_range_empty_from(pre, &range, i)
            ]
            pre.wf()
            && post.wf()
            && range.wf()
            && 0 <= i < range.len
            && insert_va == range.view().spec_index(i)
            && post.kernel_l4_end == pre.kernel_l4_end
            && post.mapping_4k() == pre.mapping_4k().insert(insert_va, entry)
            && post.mapping_2m() == pre.mapping_2m()
            && post.mapping_1g() == pre.mapping_1g()
            && mmap_4k_range_empty_from(pre, &range, i)
            ==> mmap_4k_range_empty_from(post, &range, i + 1),
{
    assert forall|
        pre: PageTable<PT_TYPE>,
        post: PageTable<PT_TYPE>,
        range: VaRange4K,
        i: int,
        insert_va: VAddr,
        entry: MapEntry,
    |
        #![trigger
            mmap_4k_range_empty_from(post, &range, i + 1),
            pre.mapping_4k().insert(insert_va, entry)
        ]
        #![trigger
            post.mapping_4k().spec_index(
                range.view().spec_index(i),
            ),
            pre.mapping_4k().insert(insert_va, entry),
            mmap_4k_range_empty_from(pre, &range, i)
        ]
        pre.wf()
        && post.wf()
        && range.wf()
        && 0 <= i < range.len
        && insert_va == range.view().spec_index(i)
        && post.kernel_l4_end == pre.kernel_l4_end
        && post.mapping_4k() == pre.mapping_4k().insert(insert_va, entry)
        && post.mapping_2m() == pre.mapping_2m()
        && post.mapping_1g() == pre.mapping_1g()
        && mmap_4k_range_empty_from(pre, &range, i)
        implies mmap_4k_range_empty_from(post, &range, i + 1) by {
        assert forall|j: int|
            #![trigger range.view().spec_index(j)]
            i + 1 <= j < range.len implies {
                let va = range.view().spec_index(j);
                let indices = spec_va2index(va);
                &&& post.kernel_l4_end <= indices.0 < 512
                &&& 0 <= indices.1 < 512
                &&& 0 <= indices.2 < 512
                &&& 0 <= indices.3 < 512
                &&& post.spec_4k_entry_useable(
                    indices.0,
                    indices.1,
                    indices.2,
                    indices.3,
                )
            } by {
                let va = range.view().spec_index(j);
                let indices = spec_va2index(va);
                assert(va != range.view().spec_index(i)) by { seq_index_lemma::<VAddr>(); };
                assert(!post.mapping_4k().dom().contains(va)) by {
                    broadcast use PageTable::reveal_page_table_wf;
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                    broadcast use vstd::map::group_map_lemmas;
                    va_lemma();
                };
                assert(!post.mapping_2m().dom().contains(
                    spec_index2va((indices.0, indices.1, indices.2, 0)),
                )) by {
                    broadcast use PageTable::reveal_page_table_wf;
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                };
                assert(!post.mapping_1g().dom().contains(
                    spec_index2va((indices.0, indices.1, 0, 0)),
                )) by {
                    broadcast use PageTable::reveal_page_table_wf;
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                };
                assert(post.spec_4k_entry_useable(
                    indices.0,
                    indices.1,
                    indices.2,
                    indices.3,
                )) by {
                    broadcast use PageTable::reveal_page_table_wf;
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                    va_lemma();
                };
            };
    };
}

} // verus!
