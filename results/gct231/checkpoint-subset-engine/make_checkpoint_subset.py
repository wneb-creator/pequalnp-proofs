"""Create an isolated export-only bounded-subset delta from the frozen adapter."""
from pathlib import Path
base=Path(__file__).parent

def once(text,old,new):
    assert text.count(old)==1,(old,text.count(old))
    return text.replace(old,new)

text=(base/'checkpoint_basis.c').read_text()
text=once(text,'static char *pc_prefix = NULL;', '''#ifndef PNP_CHECKPOINT_DERIVED_TERMS
#define PNP_CHECKPOINT_DERIVED_TERMS 1000000
#endif
#if PNP_CHECKPOINT_DERIVED_TERMS < 1 || PNP_CHECKPOINT_DERIVED_TERMS > 1000000
#error Invalid checkpoint derived-term budget
#endif
typedef struct {
    len_t index;
    int64_t length, leading_degree;
} pc_row_choice;

static int pc_compare_rows(const void *left, const void *right) {
    const pc_row_choice *a=left, *b=right;
    if (a->leading_degree != b->leading_degree)
        return a->leading_degree < b->leading_degree ? -1 : 1;
    if (a->length != b->length) return a->length < b->length ? -1 : 1;
    return a->index < b->index ? -1 : a->index > b->index;
}

static char *pc_prefix = NULL;''')
text=once(text,'''    int64_t basis_rows=0, basis_terms=0;
    for (len_t i=0;i<bs->lml;i++) {
        int64_t length=pc_row_length(bs,bs->hm[bs->lmps[i]],md);
        if (length) { basis_rows++; basis_terms+=length; }
    }
    if (basis_rows+pc_m > 100000 || basis_terms+pc_terms > 10000000)
        pc_fail("restart input would exceed validated wrapper bounds");''', '''    int64_t available_rows=0, available_terms=0;
    pc_row_choice *choices=malloc((size_t)(bs->lml ? bs->lml : 1)*sizeof(*choices));
    if (!choices) pc_fail("row selection allocation");
    for (len_t i=0;i<bs->lml;i++) {
        hm_t *row=bs->hm[bs->lmps[i]];
        int64_t length=pc_row_length(bs,row,md);
        if (!length) continue;
        int64_t degree=0;
        const exp_t *exponent=bs->ht->ev[row[OFFSET]];
        for (len_t k=1;k<bs->ht->evl;k++)
            if (k!=bs->ht->ebl) degree+=exponent[k];
        choices[available_rows++]=(pc_row_choice){i,length,degree};
        available_terms+=length;
    }
    qsort(choices,(size_t)available_rows,sizeof(*choices),pc_compare_rows);
    int64_t basis_rows=0, basis_terms=0;
    for (int64_t i=0;i<available_rows;i++) {
        if (choices[i].length > PNP_CHECKPOINT_DERIVED_TERMS-basis_terms) continue;
        if (basis_rows+pc_m >= 100000) continue;
        choices[basis_rows++]=choices[i];
        basis_terms+=choices[i].length;
    }
    if (basis_rows+pc_m > 100000 || basis_terms+pc_terms > 10000000)
        pc_fail("restart input would exceed validated wrapper bounds");''')
text=once(text,'''    for (len_t i=0;i<bs->lml;i++) {
        int64_t length=pc_row_length(bs,bs->hm[bs->lmps[i]],md);
        if (length) fprintf(file," %" PRId64,length);
    }''', '''    for (int64_t i=0;i<basis_rows;i++)
        fprintf(file," %" PRId64,choices[i].length);''')
text=once(text,'''    for (len_t i=0;i<bs->lml;i++) {
        hm_t *row=bs->hm[bs->lmps[i]];
        if (!row) continue;''', '''    for (int64_t i=0;i<basis_rows;i++) {
        hm_t *row=bs->hm[bs->lmps[choices[i].index]];''')
text=once(text,r'''        ",\"appended_basis_terms\":%" PRId64 ","
        "\"scope\":\"Original generators plus current active polynomial consequences; not a Groebner verdict.\"}\n",
        sequence,round,pc_field,pc_n,pc_m,pc_terms,basis_rows,basis_terms);''', r'''        ",\"appended_basis_terms\":%" PRId64 ","
        "\"available_basis_rows\":%" PRId64 ",\"available_basis_terms\":%" PRId64 ","
        "\"omitted_basis_rows\":%" PRId64 ",\"omitted_basis_terms\":%" PRId64 ","
        "\"derived_term_budget\":%d,"
        "\"selection\":\"Increasing leading degree, then term count, then active-basis index; greedy budget.\","
        "\"scope\":\"Original generators plus a bounded subset of active polynomial consequences; partial restart generating set, not a Groebner verdict.\"}\n",
        sequence,round,pc_field,pc_n,pc_m,pc_terms,basis_rows,basis_terms,
        available_rows,available_terms,available_rows-basis_rows,
        available_terms-basis_terms,PNP_CHECKPOINT_DERIVED_TERMS);''')
text=once(text,'    free(temporary);free(complete);free(meta_tmp);free(meta);',
    '    free(choices);free(temporary);free(complete);free(meta_tmp);free(meta);')
text=text.replace(' * basis rows. It is a restart input, never a Groebner-basis certificate.',
                  ' * basis rows up to a derived-term budget. It is only a partial restart input.')
(base/'checkpoint_basis_subset.c').write_text(text)
maker=(base/'make_checkpoint_engine.py').read_text()
maker=once(maker,"target=base/'checkpoint'","target=base/'checkpoint-subset'")
maker=once(maker,"base/'checkpoint_basis.c'","base/'checkpoint_basis_subset.c'")
(base/'make_checkpoint_subset_engine.py').write_text(maker)
runner=(base/'run_neogb_checkpoint.py').read_text()
runner=once(runner,"directory=Path(__file__).parent/'checkpoint'",
                   "directory=Path(__file__).parent/'checkpoint-subset'")
(base/'run_neogb_checkpoint_subset.py').write_text(runner)
controls=(base/'checkpoint_controls.py').read_text()
controls=once(controls,"out=base/'checkpoint/controls-v2'", "out=base/'checkpoint-subset/controls'")
controls=once(controls,"runner=base/'run_neogb_checkpoint.py'", "runner=base/'run_neogb_checkpoint_subset.py'")
controls=once(controls,"        for result in (full,stopped,resumed):", '''        for result in (full,stopped,resumed):
            meta=result['checkpoint']['metadata']
            assert meta['appended_basis_terms'] <= meta['derived_term_budget']
            assert meta['available_basis_rows'] == meta['appended_basis_rows'] + meta['omitted_basis_rows']
            assert meta['available_basis_terms'] == meta['appended_basis_terms'] + meta['omitted_basis_terms']''')
(base/'checkpoint_subset_controls.py').write_text(controls)
print('Generated isolated bounded-subset source, engine maker, runner, and controls.')
