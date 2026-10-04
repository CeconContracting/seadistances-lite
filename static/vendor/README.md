# Vendored front-end libraries

Served from here instead of a CDN, so the UI works offline and on networks
that block cdnjs (the routing never needed the internet; the page did).

| Library | Version | Licence | Used for |
|---|---|---|---|
| Leaflet | 1.9.4 | BSD-2-Clause (`leaflet/LICENSE`) | the map |
| SortableJS | 1.15.2 | MIT (`sortable/LICENSE`) | drag-to-reorder route list |
| MapLibre GL JS | 5.24.0 | BSD-3-Clause (`maplibre/LICENSE.txt`) | globe view, loaded only when opened |

To update: `npm install leaflet@x sortablejs@y maplibre-gl@z`, copy the
`dist` files over these, and update this table.
