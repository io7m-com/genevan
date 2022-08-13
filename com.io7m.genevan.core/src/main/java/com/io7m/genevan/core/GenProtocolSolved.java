/*
 * Copyright © 2022 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

package com.io7m.genevan.core;

import com.io7m.jaffirm.core.Preconditions;

import java.util.Objects;

/**
 * A solved version negotiation.
 *
 * @param clientHandler  The client handler that will be used
 * @param serverEndpoint The server endpoint that will be used
 *
 * @param <C> The type of client handlers
 * @param <S> The type of server endpoints
 */

public record GenProtocolSolved<
  C extends GenProtocolClientHandlerType,
  S extends GenProtocolServerEndpointType>(
  C clientHandler,
  S serverEndpoint)
{
  /**
   * A solved version negotiation.
   *
   * @param clientHandler  The client handler that will be used
   * @param serverEndpoint The server endpoint that will be used
   */

  public GenProtocolSolved
  {
    Objects.requireNonNull(clientHandler, "clientHandler");
    Objects.requireNonNull(serverEndpoint, "server");

    Preconditions.checkPrecondition(
      clientHandler.isCompatibleWith(serverEndpoint),
      "Client handle must be compatible with server endpoint."
    );
    Preconditions.checkPrecondition(
      serverEndpoint.isCompatibleWith(clientHandler),
      "Server endpoint must be compatible with client handler."
    );
  }
}
