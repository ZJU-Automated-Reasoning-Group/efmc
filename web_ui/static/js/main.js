/**
 * Main JavaScript file for EFMC & EFSMT Web UI
 */

document.addEventListener('DOMContentLoaded', function() {
    // Add active class to current nav item
    const currentPath = window.location.pathname;
    document.querySelectorAll('.navbar-nav .nav-link').forEach(link => {
        if (link.getAttribute('href') === currentPath) {
            link.classList.add('active');
        } else {
            link.classList.remove('active');
        }
    });

    // Initialize tooltips
    const tooltipTriggerList = [].slice.call(document.querySelectorAll('[data-bs-toggle="tooltip"]'));
    tooltipTriggerList.map(function (tooltipTriggerEl) {
        return new bootstrap.Tooltip(tooltipTriggerEl);
    });

    // Add syntax highlighting to pre code blocks
    document.querySelectorAll('pre code').forEach((block) => {
        if (typeof hljs !== 'undefined') {
            hljs.highlightBlock(block);
        }
    });

    // Handle tab navigation via URL hash
    function handleTabNavigation() {
        const hash = window.location.hash;
        if (hash) {
            const tabId = hash.substring(1);
            const tabElement = document.getElementById(tabId + '-tab');
            if (tabElement) {
                tabElement.click();
            }
        }
    }

    // Call on page load
    handleTabNavigation();

    // Listen for hash changes
    window.addEventListener('hashchange', handleTabNavigation);

    // Update hash when tabs are clicked
    document.querySelectorAll('[data-bs-toggle="tab"]').forEach(tab => {
        tab.addEventListener('shown.bs.tab', function (e) {
            const id = e.target.getAttribute('aria-controls');
            history.replaceState(null, null, '#' + id);
        });
    });

    // Add engine class to result container based on selected engine
    const engineSelect = document.getElementById('engineSelect');
    if (engineSelect) {
        engineSelect.addEventListener('change', function() {
            const resultContainer = document.getElementById('resultContainer');
            if (resultContainer) {
                // Remove all engine classes
                resultContainer.classList.remove('engine-ef', 'engine-pdr', 'engine-kind', 'engine-houdini');
                // Add the selected engine class
                resultContainer.classList.add('engine-' + this.value);
            }
        });
        
        // Initialize with current value
        if (document.getElementById('resultContainer')) {
            document.getElementById('resultContainer').classList.add('engine-' + engineSelect.value);
        }
    }
}); 