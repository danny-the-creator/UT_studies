package ss.project.client;

/**
 * Represents interface for the client himself. (ClientTUI)
 */
public interface ClientListener {
    /**
     * Called when the connection to the chat server is lost.
     */
    public void connectionLost();
}
