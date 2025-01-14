package ss.week7.chat.client;

import java.io.FileNotFoundException;
import java.io.IOException;

public interface ClientListener {
    /**
     * Called when a new chat message is received.
     *
     * @param name The name of the sender.
     * @param message The content of the chat message.
     */
    public void chatMessage(String name, String message);

    /**
     * Called when the connection to the chat server is lost.
     */
    public void connectionLost();
}