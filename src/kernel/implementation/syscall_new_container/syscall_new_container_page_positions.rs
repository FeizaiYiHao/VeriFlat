use vstd::assert_sets_equal;
use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) proof fn new_container_nine_page_positions_distinct(pages: Seq<PagePtr>)
    requires
        pages.len() == 9,
        pages.no_duplicates(),
    ensures
        pages.spec_index(1) != pages.spec_index(0),
        pages.spec_index(2) != pages.spec_index(0),
        pages.spec_index(2) != pages.spec_index(1),
        pages.spec_index(3) != pages.spec_index(0),
        pages.spec_index(3) != pages.spec_index(1),
        pages.spec_index(3) != pages.spec_index(2),
        pages.spec_index(8) != pages.spec_index(0),
        pages.spec_index(8) != pages.spec_index(1),
        pages.spec_index(8) != pages.spec_index(2),
        pages.spec_index(8) != pages.spec_index(3),
        pages.spec_index(4) != pages.spec_index(0),
        pages.spec_index(4) != pages.spec_index(1),
        pages.spec_index(4) != pages.spec_index(2),
        pages.spec_index(4) != pages.spec_index(3),
        pages.spec_index(4) != pages.spec_index(8),
        pages.spec_index(5) != pages.spec_index(0),
        pages.spec_index(5) != pages.spec_index(1),
        pages.spec_index(5) != pages.spec_index(2),
        pages.spec_index(5) != pages.spec_index(3),
        pages.spec_index(5) != pages.spec_index(8),
        pages.spec_index(5) != pages.spec_index(4),
        pages.spec_index(6) != pages.spec_index(0),
        pages.spec_index(6) != pages.spec_index(1),
        pages.spec_index(6) != pages.spec_index(2),
        pages.spec_index(6) != pages.spec_index(3),
        pages.spec_index(6) != pages.spec_index(8),
        pages.spec_index(6) != pages.spec_index(4),
        pages.spec_index(6) != pages.spec_index(5),
        pages.spec_index(7) != pages.spec_index(0),
        pages.spec_index(7) != pages.spec_index(1),
        pages.spec_index(7) != pages.spec_index(2),
        pages.spec_index(7) != pages.spec_index(3),
        pages.spec_index(7) != pages.spec_index(8),
        pages.spec_index(7) != pages.spec_index(4),
        pages.spec_index(7) != pages.spec_index(5),
        pages.spec_index(7) != pages.spec_index(6),
{
    reveal(Seq::no_duplicates);
}

pub(super) proof fn new_container_nine_page_positions_wf(pages: Seq<PagePtr>)
    requires
        pages.len() == 9,
        pages.no_duplicates(),
    ensures
        pages.to_set().contains(pages.spec_index(0)),
        pages.to_set().contains(pages.spec_index(1)),
        pages.to_set().contains(pages.spec_index(2)),
        pages.to_set().contains(pages.spec_index(3)),
        pages.to_set().contains(pages.spec_index(4)),
        pages.to_set().contains(pages.spec_index(5)),
        pages.to_set().contains(pages.spec_index(6)),
        pages.to_set().contains(pages.spec_index(7)),
        pages.to_set().contains(pages.spec_index(8)),
        pages.spec_index(1) != pages.spec_index(0),
        pages.spec_index(2) != pages.spec_index(0),
        pages.spec_index(2) != pages.spec_index(1),
        pages.spec_index(3) != pages.spec_index(0),
        pages.spec_index(3) != pages.spec_index(1),
        pages.spec_index(3) != pages.spec_index(2),
        pages.spec_index(8) != pages.spec_index(0),
        pages.spec_index(8) != pages.spec_index(1),
        pages.spec_index(8) != pages.spec_index(2),
        pages.spec_index(8) != pages.spec_index(3),
        pages.spec_index(4) != pages.spec_index(0),
        pages.spec_index(4) != pages.spec_index(1),
        pages.spec_index(4) != pages.spec_index(2),
        pages.spec_index(4) != pages.spec_index(3),
        pages.spec_index(4) != pages.spec_index(8),
        pages.spec_index(5) != pages.spec_index(0),
        pages.spec_index(5) != pages.spec_index(1),
        pages.spec_index(5) != pages.spec_index(2),
        pages.spec_index(5) != pages.spec_index(3),
        pages.spec_index(5) != pages.spec_index(8),
        pages.spec_index(5) != pages.spec_index(4),
        pages.spec_index(6) != pages.spec_index(0),
        pages.spec_index(6) != pages.spec_index(1),
        pages.spec_index(6) != pages.spec_index(2),
        pages.spec_index(6) != pages.spec_index(3),
        pages.spec_index(6) != pages.spec_index(8),
        pages.spec_index(6) != pages.spec_index(4),
        pages.spec_index(6) != pages.spec_index(5),
        pages.spec_index(7) != pages.spec_index(0),
        pages.spec_index(7) != pages.spec_index(1),
        pages.spec_index(7) != pages.spec_index(2),
        pages.spec_index(7) != pages.spec_index(3),
        pages.spec_index(7) != pages.spec_index(8),
        pages.spec_index(7) != pages.spec_index(4),
        pages.spec_index(7) != pages.spec_index(5),
        pages.spec_index(7) != pages.spec_index(6),
        new_container_bootstrap_4k_pages(
            pages.spec_index(0),
            pages.spec_index(1),
            pages.spec_index(2),
            pages.spec_index(3),
            pages.spec_index(8),
            pages.spec_index(4),
            pages.spec_index(5),
            pages.spec_index(6),
        ).len() == 8,
        !new_container_bootstrap_4k_pages(
            pages.spec_index(0),
            pages.spec_index(1),
            pages.spec_index(2),
            pages.spec_index(3),
            pages.spec_index(8),
            pages.spec_index(4),
            pages.spec_index(5),
            pages.spec_index(6),
        ).contains(pages.spec_index(7)),
        pages.to_set()
            == new_container_bootstrap_4k_pages(
                pages.spec_index(0),
                pages.spec_index(1),
                pages.spec_index(2),
                pages.spec_index(3),
                pages.spec_index(8),
                pages.spec_index(4),
                pages.spec_index(5),
                pages.spec_index(6),
            ).union(seq![pages.spec_index(7)].to_set()),
        pages.to_set()
            == new_container_bootstrap_4k_pages(
                pages.spec_index(0),
                pages.spec_index(1),
                pages.spec_index(2),
                pages.spec_index(3),
                pages.spec_index(8),
                pages.spec_index(4),
                pages.spec_index(5),
                pages.spec_index(6),
            ).insert(pages.spec_index(7)),
{
    new_container_nine_page_positions_distinct(pages);
    pages.to_set_ensures();
    let bootstrap_pages = new_container_bootstrap_4k_pages(
        pages.spec_index(0),
        pages.spec_index(1),
        pages.spec_index(2),
        pages.spec_index(3),
        pages.spec_index(8),
        pages.spec_index(4),
        pages.spec_index(5),
        pages.spec_index(6),
    );
    let bootstrap_seq = seq![
        pages.spec_index(0),
        pages.spec_index(1),
        pages.spec_index(2),
        pages.spec_index(3),
        pages.spec_index(8),
        pages.spec_index(4),
        pages.spec_index(5),
        pages.spec_index(6),
    ];
    assert(bootstrap_seq.no_duplicates()) by {
        reveal(Seq::no_duplicates);
    };
    bootstrap_seq.unique_seq_to_set();
    assert(bootstrap_pages == bootstrap_seq.to_set()) by {
        reveal(new_container_bootstrap_4k_pages);
    };
    assert(bootstrap_pages.len() == 8) by {
        bootstrap_seq.unique_seq_to_set();
    };
    assert(!bootstrap_pages.contains(pages.spec_index(7))) by {
        reveal(new_container_bootstrap_4k_pages);
        reveal(Seq::contains);
    };
    assert(
        pages.to_set()
            == bootstrap_pages.union(seq![pages.spec_index(7)].to_set())
    ) by {
        let thread_seq = seq![pages.spec_index(7)];
        let thread_pages = thread_seq.to_set();
        bootstrap_seq.to_set_ensures();
        thread_seq.to_set_ensures();
        assert_sets_equal!(
            pages.to_set() == bootstrap_pages.union(thread_pages),
            page_ptr => {
                reveal(new_container_bootstrap_4k_pages);
                reveal(Seq::contains);
                broadcast use vstd::set::lemma_set_union;
                if pages.to_set().contains(page_ptr) {
                    assert(pages.contains(page_ptr)) by {
                        pages.to_set_ensures();
                    };
                    pages.index_of_first_ensures(page_ptr);
                    let i = pages.index_of_first(page_ptr).unwrap();
                    assert(
                        i == 0 || i == 1 || i == 2
                            || i == 3 || i == 4 || i == 5
                            || i == 6 || i == 7 || i == 8
                    ) by {
                        pages.index_of_first_ensures(page_ptr);
                    };
                    if i == 7 {
                        assert(page_ptr == pages.spec_index(7)) by {
                            pages.index_of_first_ensures(page_ptr);
                        };
                        thread_seq.lemma_index_contains(0);
                    } else {
                        assert(bootstrap_seq.contains(page_ptr)) by {
                            reveal(Seq::contains);
                            if i == 0 {
                                assert(bootstrap_seq.spec_index(0) == page_ptr) by {
                                    pages.index_of_first_ensures(page_ptr);
                                };
                            } else if i == 1 {
                                assert(bootstrap_seq.spec_index(1) == page_ptr) by {
                                    pages.index_of_first_ensures(page_ptr);
                                };
                            } else if i == 2 {
                                assert(bootstrap_seq.spec_index(2) == page_ptr) by {
                                    pages.index_of_first_ensures(page_ptr);
                                };
                            } else if i == 3 {
                                assert(bootstrap_seq.spec_index(3) == page_ptr) by {
                                    pages.index_of_first_ensures(page_ptr);
                                };
                            } else if i == 4 {
                                assert(bootstrap_seq.spec_index(5) == page_ptr) by {
                                    pages.index_of_first_ensures(page_ptr);
                                };
                            } else if i == 5 {
                                assert(bootstrap_seq.spec_index(6) == page_ptr) by {
                                    pages.index_of_first_ensures(page_ptr);
                                };
                            } else if i == 6 {
                                assert(bootstrap_seq.spec_index(7) == page_ptr) by {
                                    pages.index_of_first_ensures(page_ptr);
                                };
                            } else {
                                assert(bootstrap_seq.spec_index(4) == page_ptr) by {
                                    pages.index_of_first_ensures(page_ptr);
                                };
                            }
                        };
                    }
                }
                if bootstrap_pages.union(thread_pages).contains(page_ptr) {
                    if bootstrap_pages.contains(page_ptr) {
                        assert(bootstrap_seq.contains(page_ptr)) by {
                            bootstrap_seq.to_set_ensures();
                        };
                        bootstrap_seq.index_of_first_ensures(page_ptr);
                        let i = bootstrap_seq
                            .index_of_first(page_ptr).unwrap();
                        assert(
                            i == 0 || i == 1 || i == 2 || i == 3
                                || i == 4 || i == 5 || i == 6 || i == 7
                        ) by {
                            bootstrap_seq.index_of_first_ensures(page_ptr);
                        };
                        if i == 0 {
                            assert(page_ptr == pages.spec_index(0)) by {
                                bootstrap_seq.index_of_first_ensures(page_ptr);
                            };
                        } else if i == 1 {
                            assert(page_ptr == pages.spec_index(1)) by {
                                bootstrap_seq.index_of_first_ensures(page_ptr);
                            };
                        } else if i == 2 {
                            assert(page_ptr == pages.spec_index(2)) by {
                                bootstrap_seq.index_of_first_ensures(page_ptr);
                            };
                        } else if i == 3 {
                            assert(page_ptr == pages.spec_index(3)) by {
                                bootstrap_seq.index_of_first_ensures(page_ptr);
                            };
                        } else if i == 4 {
                            assert(page_ptr == pages.spec_index(8)) by {
                                bootstrap_seq.index_of_first_ensures(page_ptr);
                            };
                        } else if i == 5 {
                            assert(page_ptr == pages.spec_index(4)) by {
                                bootstrap_seq.index_of_first_ensures(page_ptr);
                            };
                        } else if i == 6 {
                            assert(page_ptr == pages.spec_index(5)) by {
                                bootstrap_seq.index_of_first_ensures(page_ptr);
                            };
                        } else {
                            assert(page_ptr == pages.spec_index(6)) by {
                                bootstrap_seq.index_of_first_ensures(page_ptr);
                            };
                        }
                        assert(pages.to_set().contains(page_ptr)) by {
                            pages.to_set_ensures();
                        };
                    } else {
                        assert(thread_seq.contains(page_ptr)) by {
                            thread_seq.to_set_ensures();
                        };
                        assert(page_ptr == pages.spec_index(7)) by {
                            reveal(Seq::contains);
                        };
                        assert(pages.to_set().contains(page_ptr)) by {
                            pages.to_set_ensures();
                        };
                    }
                }
            }
        );
    };
    assert(pages.to_set() == bootstrap_pages.insert(pages.spec_index(7))) by {
        let thread_seq = seq![pages.spec_index(7)];
        thread_seq.to_set_ensures();
        assert_sets_equal!(
            pages.to_set() == bootstrap_pages.insert(pages.spec_index(7)),
            page_ptr => {
                reveal(Seq::contains);
                broadcast use vstd::set::lemma_set_union;
                broadcast use vstd::set::lemma_set_insert_same;
                broadcast use vstd::set::lemma_set_insert_different;
            }
        );
    };
}


}
