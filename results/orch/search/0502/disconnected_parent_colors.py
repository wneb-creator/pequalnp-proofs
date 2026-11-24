def disconnected_parents(c, aa, bb, base_count=15, internal_count=9, output_count=5):
    parent_count=base_count+internal_count
    assert len(aa)==len(bb)==internal_count+output_count
    parent_colors=[c.var() for _ in range(parent_count)]
    edge_colors=[c.var() for _ in range(output_count)]
    for j,edge in enumerate(edge_colors):
        for selectors in (aa[internal_count+j],bb[internal_count+j]):
            for selected,parent in zip(selectors[:parent_count],parent_colors):
                c.add(-selected,-parent,edge)
                c.add(-selected,parent,-edge)
    c.add(-edge_colors[0])
    c.add(*edge_colors[1:])
    return parent_colors,edge_colors
