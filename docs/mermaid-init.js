// Initialize Mermaid when document is ready
if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', function() {
        if (typeof mermaid !== 'undefined') {
            mermaid.contentLoaded();
        }
    });
} else {
    if (typeof mermaid !== 'undefined') {
        mermaid.contentLoaded();
    }
}
